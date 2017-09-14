package cspSolver;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.Iterator;
import java.util.List;

import sudoku.Converter;
import sudoku.SudokuFile;

/**
 * Backtracking solver.
 *
 */
public class BTSolver implements Runnable {

	// ===============================================================================
	// Properties
	// ===============================================================================

	private ConstraintNetwork network;
	private static Trail trail = Trail.getTrail();
	private boolean hasSolution = false;
	private SudokuFile sudokuGrid;

	private int numAssignments;
	private int numBacktracks;
	private long startTime;
	private long endTime;

	public enum VariableSelectionHeuristic {
		None, MinimumRemainingValue, Degree
	};

	public enum ValueSelectionHeuristic {
		None, LeastConstrainingValue
	};

	public enum ConsistencyCheck {
		None, ForwardChecking, ArcConsistency
	};

	public enum NakedCheck {
		None, NakedPairs, NakedTriples
	};

	private VariableSelectionHeuristic varHeuristics;
	private ValueSelectionHeuristic valHeuristics;
	private ConsistencyCheck cChecks;
	private NakedCheck nChecks;
	// ===============================================================================
	// Constructors
	// ===============================================================================

	public BTSolver(SudokuFile sf) {
		this.network = Converter.SudokuFileToConstraintNetwork(sf);
		this.sudokuGrid = sf;
		numAssignments = 0;
		numBacktracks = 0;
	}

	// ===============================================================================
	// Modifiers
	// ===============================================================================

	public void setVariableSelectionHeuristic(VariableSelectionHeuristic vsh) {
		this.varHeuristics = vsh;
	}

	public void setValueSelectionHeuristic(ValueSelectionHeuristic vsh) {
		this.valHeuristics = vsh;
	}

	public void setConsistencyChecks(ConsistencyCheck cc) {
		this.cChecks = cc;
	}

	public void setNakedConsistency(NakedCheck nck) {
		this.nChecks = nck;
	}
	// ===============================================================================
	// Accessors
	// ===============================================================================

	/**
	 * @return true if a solution has been found, false otherwise.
	 */
	public boolean hasSolution() {
		return hasSolution;
	}

	/**
	 * @return solution if a solution has been found, otherwise returns the
	 *         unsolved puzzle.
	 */
	public SudokuFile getSolution() {
		return sudokuGrid;
	}

	public void printSolverStats() {
		System.out.println("Time taken:" + (endTime - startTime) + " ms");
		System.out.println("Number of assignments: " + numAssignments);
		System.out.println("Number of backtracks: " + numBacktracks);
	}

	/**
	 * 
	 * @return time required for the solver to attain in seconds
	 */
	public long getTimeTaken() {
		return endTime - startTime;
	}

	public int getNumAssignments() {
		return numAssignments;
	}

	public int getNumBacktracks() {
		return numBacktracks;
	}

	public ConstraintNetwork getNetwork() {
		return network;
	}

	// ===============================================================================
	// Helper Methods
	// ===============================================================================

	/**
	 * Checks whether the changes from the last time this method was called are
	 * consistent.
	 * 
	 * @return true if consistent, false otherwise
	 */
	private boolean checkConsistency() {
		boolean isConsistent = false;
		switch (cChecks) {
		case None:
			isConsistent = assignmentsCheck();
			break;
		case ForwardChecking:
			isConsistent = forwardChecking();
			break;
		case ArcConsistency:
			isConsistent = arcConsistency();
			break;
		default:
			isConsistent = assignmentsCheck();
			break;
		}
		return isConsistent;
	}

	/**
	 * Checks whether the changes from the last time this method was called are
	 * consistent.
	 * 
	 * @return true if consistent, false otherwise
	 */
	private boolean checkNakedConsistency() {
		boolean isConsistent = false;
		switch (nChecks) {
		case None:
			isConsistent = true;
			break;
		case NakedPairs:
			isConsistent = nakedPairs();
			break;
		case NakedTriples:
			isConsistent = nakedTriples();
			break;
		default:
			isConsistent = true;
			break;
		}
		return isConsistent;
	}

	/**
	 * default consistency check. Ensures no two variables are assigned to the
	 * same value.
	 * 
	 * @return true if consistent, false otherwise.
	 */
	private boolean assignmentsCheck() {
		for (Variable v : network.getVariables()) {
			if (v.isAssigned()) {
				for (Variable vOther : network.getNeighborsOfVariable(v)) {
					if (v.getAssignment() == vOther.getAssignment()) {
						return false;
					}
				}
			}
		}
		return true;
	}

	/**
	 * TODO: Implement forward checking.
	 */
	private boolean forwardChecking() {
		Variable assignedVariable;
		List<Constraint> modifiedConstraints = network.getModifiedConstraints();
		for (int i = 0; i < modifiedConstraints.size(); i++) {
			List<Variable> variableList = modifiedConstraints.get(i).vars;
			for (int j = 0; j < variableList.size(); j++) {
				if (variableList.get(j).isAssigned()) {
					assignedVariable = variableList.get(j);
					for (int k = 0; k < modifiedConstraints.size(); k++) {
						if (modifiedConstraints.get(k).contains(assignedVariable)) {
							for (int l = 0; l < modifiedConstraints.get(k).vars.size(); l++) {
								if (modifiedConstraints.get(k).vars.get(l) != assignedVariable) {
									modifiedConstraints.get(k).vars.get(l)
											.removeValueFromDomain(assignedVariable.getAssignment());
									if (modifiedConstraints.get(k).vars.get(l).getDomain().size() == 0) {
										return false;
									}
								}
							}
						}
					}
				}
			}
		}
		return true;
	}

	/**
	 * TODO: Implement Maintaining Arc Consistency.
	 * Arc Consistency ensures that every value selection for every variable selection is valid
	 */
	private boolean arcConsistency() {
		List<Constraint> mod = network.getModifiedConstraints();
		int[] rem;
		for (Constraint c : mod) {
			for (Variable x : c.vars) {
				rem = new int[sudokuGrid.getN() + 1];
				for (Variable y : c.vars) {
					if (x.equals(y))
						continue;
					for (Integer i : x.getDomain()) {
						boolean valid = false;
						for (Integer j : y.getDomain()) {
							if (i != j) {
								valid = true;
								continue;
							}
						}
						if (!valid) {
							rem[i] = 1;
						}
					}
				}
				for (int i = 1; i < rem.length; i++) {
					if (rem[i] == 1 && x.getDomain().contains(i)) {
						x.removeValueFromDomain(i);
					}
					if (x.size() == 0) {
						return false;
					}

				}
			}
			mod = network.getModifiedConstraints();
		}
		return true;
	}

	private boolean nakedPairs() {
		List<Variable> allVariables = network.getVariables();
		for (Variable v : allVariables) {
			boolean sameBlock = false;
			boolean sameCol = false;
			boolean sameRow = false;
			if (v.size() == 2) {
				List<Variable> neighbors = network.getNeighborsOfVariable(v);
				Variable match = v;
				Domain domainOfV = v.getDomain();
				for (Variable n : neighbors) {
					if (v.getName() != n.getName() && n.size() == 2) {
						for (int i : domainOfV) {
							if (!n.getDomain().contains(i)) {
								match = v;
								break;
							}
							match = n;
						}
					}
				}
				if (v.getName() != match.getName()) {
					if (v.block() == match.block())
						sameBlock = true;
					if (v.col() == match.col())
						sameCol = true;
					if (v.row() == match.row())
						sameRow = true;
					for (Variable n : neighbors) {
						if (n.getName() != v.getName() && n.getName() != match.getName()) {
							if ((sameBlock && v.block() == n.block()) || (sameCol && v.col() == n.col())
									|| (sameRow && v.row() == n.row())) {
								for (int i : domainOfV) {
									n.getDomain().remove(i);
									if (n.size() == 0) {
										return false;
									}
								}
							}
						}
					}
				}
			}
		}
		return true;
	}

	private boolean nakedTriples() {
		List<Variable> allVariables = network.getVariables();
		List<Variable> twosAndThrees = new ArrayList<Variable>();
		for (Variable v : allVariables) {
			if (v.size() == 2 || v.size() == 3) {
				twosAndThrees.add(v);
			}
		}
		if (twosAndThrees.size() >= 3) {
			for (int i = 0; i < twosAndThrees.size() - 2; i++) {
				List<Variable> neighbors = network.getNeighborsOfVariable(twosAndThrees.get(i));
				for (int j = i + 1; j < twosAndThrees.size() - 1; j++) {
					for (int k = j + 1; k < twosAndThrees.size(); k++) {
						if (!neighbors.contains(twosAndThrees.get(j))) {
							break;
						}
						if (neighbors.contains(twosAndThrees.get(k))) {
							if (twosAndThrees.get(i).size() == 2 && twosAndThrees.get(j).size() == 2
									&& twosAndThrees.get(k).size() == 2) {
								if (twosAndThrees.get(i).getDomain().getValues() == twosAndThrees.get(j).getDomain()
										.getValues()
										|| twosAndThrees.get(i).getDomain().getValues() == twosAndThrees.get(k)
												.getDomain().getValues()
										|| twosAndThrees.get(j).getDomain().getValues() == twosAndThrees.get(k)
												.getDomain().getValues()) {
									break;
								}
							}
							Domain combine = new Domain(twosAndThrees.get(i).getDomain());
							for (int d : twosAndThrees.get(j).getDomain()) {
								if (!combine.contains(d))
									combine.getValues().add(d);
							}
							for (int d : twosAndThrees.get(k).getDomain()) {
								if (!combine.contains(d))
									combine.getValues().add(d);
							}
							if (combine.size() > 3) {
								break;
							}
							boolean sameCol = (twosAndThrees.get(i).col() == twosAndThrees.get(j).col()
									&& twosAndThrees.get(i).col() == twosAndThrees.get(k).col());
							boolean sameRow = (twosAndThrees.get(i).row() == twosAndThrees.get(j).row()
									&& twosAndThrees.get(i).row() == twosAndThrees.get(k).row());
							boolean sameBlock = (twosAndThrees.get(i).block() == twosAndThrees.get(j).block()
									&& twosAndThrees.get(i).block() == twosAndThrees.get(k).block());
							for (Variable n : neighbors) {
								if (!n.isAssigned() && n.getName() != twosAndThrees.get(j).getName()
										&& n.getName() != twosAndThrees.get(k).getName()) {
									if (sameCol && twosAndThrees.get(i).col() == n.col()
											|| sameRow && twosAndThrees.get(i).row() == n.row()
											|| sameBlock && twosAndThrees.get(i).block() == n.block()) {
										for (int d : twosAndThrees.get(i).getDomain()) {
											n.removeValueFromDomain(d);
										}
										for (int d : twosAndThrees.get(j).getDomain()) {
											n.removeValueFromDomain(d);
										}
										for (int d : twosAndThrees.get(k).getDomain()) {
											n.removeValueFromDomain(d);
										}
										if (n.size() == 0) {
											return false;
										}
									}
								}
							}
						}
					}
				}
			}
		}
		return true;
	}

	/**
	 * Selects the next variable to check.
	 * 
	 * @return next variable to check. null if there are no more variables to
	 *         check.
	 */
	private Variable selectNextVariable() {
		Variable next = null;
		switch (varHeuristics) {
		case None:
			next = getfirstUnassignedVariable();
			break;
		case MinimumRemainingValue:
			next = getMRV();
			break;
		case Degree:
			next = getDegree();
			break;
		default:
			next = getfirstUnassignedVariable();
			break;
		}
		return next;
	}

	/**
	 * default next variable selection heuristic. Selects the first unassigned
	 * variable.
	 * 
	 * @return first unassigned variable. null if no variables are unassigned.
	 */
	private Variable getfirstUnassignedVariable() {
		for (Variable v : network.getVariables()) {
			if (!v.isAssigned()) {
				return v;
			}
		}
		return null;
	}

	/**
	 * TODO: Implement MRV heuristic
	 * 
	 * @return variable with minimum remaining values that isn't assigned, null
	 *         if all variables are assigned.
	 */
	private Variable getMRV() {
		Variable smallest = null;
		int min = sudokuGrid.getN();
		for (Variable v : network.getVariables()) {
			if (!v.isAssigned()) {
				if (v.size() <= min) {
					smallest = v;
					min = v.size();
				}
			}
		}
		return smallest;
	}

	/**
	 * TODO: Implement Degree heuristic
	 * 
	 * @return variable constrained by the most unassigned variables, null if
	 *         all variables are assigned.
	 */
	private Variable getDegree() {
		List<Variable> vNeighbors;
		Variable result = null;
		int max = -1;
		int degree;
		for (Variable v : network.getVariables()) {
			if (!v.isAssigned()) {
				degree = 0;
				vNeighbors = network.getNeighborsOfVariable(v);
				for (Variable x : vNeighbors) {
					if (x.equals(v))
						continue;
					if (!x.isAssigned())
						degree++;
				}
				if (degree > max) {
					max = degree;
					result = v;
				}
			}
		}
		return result;
	}

	/**
	 * Value Selection Heuristics. Orders the values in the domain of the
	 * variable passed as a parameter and returns them as a list.
	 * 
	 * @return List of values in the domain of a variable in a specified order.
	 */
	public List<Integer> getNextValues(Variable v) {
		List<Integer> orderedValues;
		switch (valHeuristics) {
		case None:
			orderedValues = getValuesInOrder(v);
			break;
		case LeastConstrainingValue:
			orderedValues = getValuesLCVOrder(v);
			break;
		default:
			orderedValues = getValuesInOrder(v);
			break;
		}
		return orderedValues;
	}

	/**
	 * Default value ordering.
	 * 
	 * @param v
	 *            Variable whose values need to be ordered
	 * @return values ordered by lowest to highest.
	 */
	public List<Integer> getValuesInOrder(Variable v) {
		List<Integer> values = v.getDomain().getValues();

		Comparator<Integer> valueComparator = new Comparator<Integer>() {

			@Override
			public int compare(Integer i1, Integer i2) {
				return i1.compareTo(i2);
			}
		};
		Collections.sort(values, valueComparator);
		return values;
	}

	/**
	 * TODO: LCV heuristic
	 */
	//Created a class Pair to keep track of index and frequency. Helps limit loops
	public class Pair implements Comparable<Pair> {
		public int index;
		public int frequency;

		public Pair(int i, int v) {
			index = i;
			frequency = v;
		}

		@Override
		public int compareTo(Pair y) {
			return Integer.valueOf(this.frequency).compareTo(y.frequency);
		}

	}

	public List<Integer> getValuesLCVOrder(Variable v) {
		// initialize an array of frequency. 
		Pair[] freq = new Pair[sudokuGrid.getN()];
		for (int i = 0; i < freq.length; i++) {
			freq[i] = new Pair(i + 1, 0);
		}

		for (Variable x : network.getNeighborsOfVariable(v)) {
			if (!x.isAssigned()) {
				for (Integer i : x.getDomain()) {
					freq[i - 1].frequency++;
				}
			}
		}

		Arrays.sort(freq);
		List<Integer> orderedLCV = new ArrayList<Integer>();
		for (int j = 0; j < freq.length; j++) {
			if (v.getDomain().contains(freq[j].index))
				orderedLCV.add(freq[j].index);
		}

		return orderedLCV;
	}

	/**
	 * Called when solver finds a solution
	 */
	private void success() {
		hasSolution = true;
		sudokuGrid = Converter.ConstraintNetworkToSudokuFile(network, sudokuGrid.getN(), sudokuGrid.getP(),
				sudokuGrid.getQ());
	}

	// ===============================================================================
	// Solver
	// ===============================================================================

	/**
	 * Method to start the solver
	 */
	public void solve() {
		startTime = System.currentTimeMillis();
		try {
			solve(0);
		} catch (VariableSelectionException e) {
			System.out.println("error with variable selection heuristic.");
		}
		endTime = System.currentTimeMillis();
		Trail.clearTrail();
	}

	/**
	 * Solver
	 * 
	 * @param level
	 *            How deep the solver is in its recursion.
	 * @throws VariableSelectionException
	 */

	private void solve(int level) throws VariableSelectionException {
		if (!Thread.currentThread().isInterrupted())

		{// Check if assignment is completed
			if (hasSolution) {
				return;
			}
			if (level == 0) {
				// arcConsistency();
			}

			// Select unassigned variable
			Variable v = selectNextVariable();

			// check if the assignment is complete
			if (v == null) {
				for (Variable var : network.getVariables()) {
					if (!var.isAssigned()) {
						throw new VariableSelectionException(
								"Something happened with the variable selection heuristic");
					}
				}
				success();
				return;
			}

			// loop through the values of the variable being checked LCV
			for (Integer i : getNextValues(v)) {
				trail.placeBreadCrumb();

				// check a value
				v.updateDomain(new Domain(i));
				numAssignments++;
				boolean isConsistent = checkConsistency() && checkNakedConsistency();

				// move to the next assignment
				if (isConsistent) {
					solve(level + 1);
				}

				// if this assignment failed at any stage, backtrack
				if (!hasSolution) {
					trail.undo();
					numBacktracks++;
				}

				else {
					return;
				}
			}
		}
	}

	@Override
	public void run() {
		solve();
	}
}
