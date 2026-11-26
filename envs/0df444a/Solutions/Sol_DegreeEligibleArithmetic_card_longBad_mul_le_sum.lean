-- Prove2me | solution 1 for DegreeEligibleArithmetic.card_longBad_mul_le_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:07:17.713286+00:00
-- url     : https://prove2.me/submissions/f6953df9-6e4e-4188-99fd-5e31cde2022c

module
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Data.Int.Star
public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.FinCases
public import Definitions.Def_BirthdayNonbacktracking_Solution

set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false
noncomputable section
variable {V : Type*} [Fintype V]
variable (d : ℕ) [NeZero d]
variable (G : SimpleGraph V) (hG : IsRegularOfDegree G d)
attribute [local instance] graphAdjDecidable
attribute [local instance] vertexDecidableEq
open DegreeEligibleArithmetic
variable {ι : Type*} [DecidableEq ι]
namespace DegreeEligibleArithmetic
theorem _root_.solution (I : Finset ι) (c : ι → ℕ) (L : ℕ) :
    (longBad I c L).card * (L + 1) ≤ ∑ i ∈ I, c i := by
  classical
  calc
    (longBad I c L).card * (L + 1) =
        ∑ _i ∈ longBad I c L, (L + 1) := by simp
    _ ≤ ∑ i ∈ longBad I c L, c i := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' := (Finset.mem_filter.mp hi).2
      omega
    _ ≤ ∑ i ∈ I, c i :=
      Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
end DegreeEligibleArithmetic
