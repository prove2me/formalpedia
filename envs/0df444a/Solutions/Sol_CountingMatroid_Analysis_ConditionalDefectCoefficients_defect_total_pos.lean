-- Prove2me | solution 1 for CountingMatroid.Analysis.ConditionalDefectCoefficients.defect_total_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:01:56.901845+00:00
-- url     : https://prove2.me/submissions/48028a5d-cfd5-46a7-a91a-c502d6d14b2f

import Definitions.Def_CountingMatroidSupport_Computation_Charged
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension2
import Definitions.Def_CountingMatroidSupport_Computation_Cost
import Definitions.Def_CountingMatroidSupport_Computation_Cost_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Dict
import Definitions.Def_CountingMatroidSupport_Computation_Heap
import Definitions.Def_CountingMatroidSupport_Computation_Machine
import Definitions.Def_CountingMatroidSupport_Computation_Machine_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Num
import Definitions.Def_CountingMatroidSupport_Computation_Queue
import Definitions.Def_CountingMatroidSupport_Computation_Rand
import Definitions.Def_CountingMatroidSupport_Computation_Roster
import Definitions.Def_CountingMatroidSupport_Computation_Slot
import Definitions.Def_CountingMatroidSupport_Computation_Space
import Definitions.Def_CountingMatroidSupport_Computation_Std
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhase
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhaseHistory
import Definitions.Def_CountingMatroid_Analysis_ConditionalDefectCoefficients
import Definitions.Def_CountingMatroid_Analysis_FirstPhaseFailure
import Definitions.Def_CountingMatroid_Analysis_InitialMultipliersGood
import Definitions.Def_CountingMatroid_Analysis_ScheduleConfidence
import Definitions.Def_CountingMatroid_Analysis_TransversalPartition
import Definitions.Def_CountingMatroid_Analysis_TransversalProjection
import Definitions.Def_CountingMatroid_Interface_Pseudocode
import Definitions.Def_CountingMatroid_Interface_Pseudocode_Extension1
import Definitions.Def_CountingMatroid_Model_Operations
import Definitions.Def_CountingMatroid_Model_Prelude
import Definitions.Def_CountingMatroid_Model_Program
import Definitions.Def_CountingMatroid_Model_Run
import Definitions.Def_CountingMatroid_Model_Subroutines
import Lean
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.BitVec
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Induction
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Set.Finite.List
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF
import Theorems.Thm_CountingMatroid_Analysis_InitialMultipliersGood_classify_defect_iff

namespace CountingMatroid.Interface
end CountingMatroid.Interface
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
namespace CountingMatroid.Analysis.TransversalRankBridge
end CountingMatroid.Analysis.TransversalRankBridge
namespace CountingMatroid.Analysis.GreedyRankCorrect
end CountingMatroid.Analysis.GreedyRankCorrect
section


set_option autoImplicit false

/-!
Conditional transversal and defect totals for the operational rank weights.
The empty assignment recovers the existing partition sums. Positivity and
binary splitting below concern these finite sums; the quadratic signature
inequalities are separate mathematical obligations.
-/

namespace CountingMatroid.Analysis.ConditionalDefectCoefficients

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.TransversalPartition

























/-- INTERNAL: The ordinary pairs of a defect completion have exactly their
prescribed/default bit; the full pair has both bits and the empty pair neither.
TEXLINE: main.tex:383-392 -/
theorem mem_defect_completion {n : ℕ} (σ : Assignment n) (index : DefectIndex n)
    (i : Fin n) (b : Bool) :
    (i, b) ∈ defectCompletion σ index ↔
      (i ≠ index.emptyPair ∧ i ≠ index.fullPair ∧ (σ i).getD false = b) ∨
        i = index.fullPair := by
  classical
  cases b <;> simp [defectCompletion] <;> tauto

/-- INTERNAL: The existing executable classifier accepts each conditioned
defect completion using the existing state-shape characterization.
TEXLINE: main.tex:383-392 -/
theorem defect_completion_classified {n : ℕ} (σ : Assignment n) (index : DefectIndex n) :
    (classifyState (defectCompletion σ index)).val =
      .defect index.emptyPair index.fullPair := by
  apply (InitialMultipliersGood.classify_defect_iff _ index).mpr
  constructor <;> intro i
  all_goals
    rw [mem_defect_completion, mem_defect_completion]
    cases hb : (σ i).getD false <;>
      by_cases he : i = index.emptyPair <;> by_cases hf : i = index.fullPair <;>
        simp_all [index.distinct, index.distinct.symm]

/-- INTERNAL: The conditioned defect completion respects the assignment
when its empty and full pairs are unassigned.
TEXLINE: main.tex:383-392 -/
theorem defect_completion_respects {n : ℕ} (σ : Assignment n) (index : DefectIndex n)
    (he : σ index.emptyPair = none) (hf : σ index.fullPair = none) :
    Respects σ (defectCompletion σ index) := by
  intro i b hb
  have hie : i ≠ index.emptyPair := by rintro rfl; rw [he] at hb; cases hb
  have hif : i ≠ index.fullPair := by rintro rfl; rw [hf] at hb; cases hb
  constructor <;> rw [mem_defect_completion]
  · simp [hie, hif, hb]
  · cases b <;> simp [hie, hif, hb]



end CountingMatroid.Analysis.ConditionalDefectCoefficients

end
set_option autoImplicit false

/-!
Conditional transversal and defect totals for the operational rank weights.
The empty assignment recovers the existing partition sums. Positivity and
binary splitting below concern these finite sums; the quadratic signature
inequalities are separate mathematical obligations.
-/

namespace CountingMatroid.Analysis.ConditionalDefectCoefficients
end CountingMatroid.Analysis.ConditionalDefectCoefficients
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ConditionalDefectCoefficients

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.TransversalPartition

/-- PAPER: main.tex:392
Conditional defect totals are positive whenever their empty and full pairs
are unassigned, as required in the paper's coefficient inequalities. -/
theorem solution {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (q : ℚ) (hq : 0 < q)
    (σ : Assignment n) (index : DefectIndex n)
    (he : σ index.emptyPair = none) (hf : σ index.fullPair = none) :
    0 < defectTotal r o₁ o₂ q σ index := by
  classical
  let S := defectCompletion σ index
  have hS : Respects σ S ∧ (classifyState S).val =
      .defect index.emptyPair index.fullPair :=
    ⟨defect_completion_respects σ index he hf, defect_completion_classified σ index⟩
  let term := fun state : PairedSet n =>
    if Respects σ state ∧
      (classifyState state).val = .defect index.emptyPair index.fullPair then
      q ^ (n - (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ state).val)
    else 0
  have hterm : 0 < term S := by
    dsimp only [term]
    rw [if_pos hS]
    exact pow_pos hq _
  exact hterm.trans_le (Finset.single_le_sum (f := term) (fun state _ => by
    dsimp only [term]
    split_ifs
    · exact (pow_pos hq _).le
    · exact le_rfl) (Finset.mem_univ S))
