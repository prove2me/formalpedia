-- Prove2me | solution 1 for CountingMatroid.Analysis.PhaseHistoryMultiplierLength.phase_history_multiplier_length_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:07:42.788238+00:00
-- url     : https://prove2.me/submissions/69481555-7755-4e90-a814-2edbfa9c4f95

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
import Definitions.Def_CountingMatroid_Analysis_EstimateMedianResource
import Definitions.Def_CountingMatroid_Analysis_PhaseResourcePrimitives
import Definitions.Def_CountingMatroid_Analysis_RationalHeight
import Definitions.Def_CountingMatroid_Analysis_ScheduleConfidence
import Definitions.Def_CountingMatroid_Analysis_ScheduleOpeningCost
import Definitions.Def_CountingMatroid_Analysis_ScheduleThermalSetupCost
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
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
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
import Theorems.Thm_CountingMatroid_Analysis_BoundedRunResourceEnvelope_observePhase_counts_le
import Theorems.Thm_CountingMatroid_Analysis_FinishPhaseWeightsSize_finishPhase_weights_length_le

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
namespace CountingMatroid.Analysis.PhaseHistoryMultiplierLength
end CountingMatroid.Analysis.PhaseHistoryMultiplierLength
namespace CountingMatroid.Analysis.FinishPhaseWeightsSize
end CountingMatroid.Analysis.FinishPhaseWeightsSize
namespace CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
end CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
namespace CountingMatroid.Analysis.LeastHalvingsCost
end CountingMatroid.Analysis.LeastHalvingsCost
namespace CountingMatroid.Analysis
end CountingMatroid.Analysis
section


set_option autoImplicit false

/-!
The phase history below is the value of each prefix of the actual bounded-run
fold, including its absorbing aborted state. Successful local ratio steps
give the product witness used by the lower-tail proof. This is a
deterministic operational representation, not a phase probability estimate.
-/

namespace CountingMatroid.Analysis.BoundedRunPhaseHistory

open CountingMatroid.Model CountingMatroid.Model.Operations
open CountingMatroid.Program CountingMatroid.Analysis.BoundedRunPhase





/-- INTERNAL: Split a charged fold at a prefix while retaining its actual value. -/
private theorem val_foldl_append {α β : Type}
    (f : β → α → Arlib.Computation.Charged Op Cell β)
    (xs ys : List α) (b : β) :
    (Arlib.Computation.Charged.foldl f (xs ++ ys) b).val =
      (Arlib.Computation.Charged.foldl f ys
        (Arlib.Computation.Charged.foldl f xs b).val).val := by
  induction xs generalizing b with
  | nil => rfl
  | cons x xs ih =>
      simpa only [List.cons_append, Arlib.Computation.Charged.val_foldl_cons]
        using ih (f b x).val

/-- INTERNAL: Consecutive history entries are related by the actual phase
body, with the previously reached tables, weights, product and bit cursor.
TEXLINE: main.tex:1160-1205 -/
theorem phaseHistory_succ {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (j : ℕ) :
    phaseHistory r o₁ o₂ tape s (j + 1) =
      (boundedRunPhase r o₁ o₂ tape s j
        (phaseHistory r o₁ o₂ tape s j)).val := by
  unfold phaseHistory Arlib.Computation.Charged.repeatFor
  rw [List.range_succ, val_foldl_append]
  rfl











end CountingMatroid.Analysis.BoundedRunPhaseHistory

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r18 · proved · represented actual phase-fold prefixes; proved their successor relation and final-output equality, reconstructed an accurate-ratio witness from successful local steps, and covered witness failure by the first failed phase. No probability estimate or unproved declaration introduced.
-/

end
set_option autoImplicit false

namespace CountingMatroid.Analysis.PhaseHistoryMultiplierLength
end CountingMatroid.Analysis.PhaseHistoryMultiplierLength
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.PhaseHistoryMultiplierLength

open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program
open CountingMatroid.Analysis.BoundedRunPhase
open CountingMatroid.Analysis.BoundedRunPhaseHistory

/-- INTERNAL: Keep the additive multiplier-scan bound through the actual
history, including writes to the learned tables. No product-size budget is
needed for a draw denominator. TEXLINE: main.tex:1356-1390 -/
theorem solution {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool)
    (s : AnnealingSchedule) (j : ℕ) (current : AnnealingCursor n)
    (h : phaseHistory r o₁ o₂ tape s j = some current) :
    (∀ index, binaryRatLength (current.currentWeights index) ≤
      6 + j * (n * n * (4 * (s.observations + 4)))) ∧
    (∀ phase index, binaryRatLength (current.tables phase index) ≤
      6 + j * (n * n * (4 * (s.observations + 4)))) := by
  induction j generalizing current with
  | zero =>
      have he : initialCursor n s = current := Option.some.inj h
      subst current
      have hfour : binaryRatLength (4 : ℚ) = 6 := by decide
      simp only [initialCursor, initialWeights, allocateLearnedWeights,
        Arlib.Computation.Charged.val_opMany, hfour, Nat.zero_mul, Nat.add_zero,
        le_refl, implies_true, and_self]
  | succ j ih =>
      rw [phaseHistory_succ] at h
      cases hp : phaseHistory r o₁ o₂ tape s j with
      | none => simp [hp, boundedRunPhase] at h
      | some previous =>
          rw [hp] at h
          obtain ⟨hw, ht⟩ := ih previous hp
          unfold boundedRunPhase at h
          simp only [Arlib.Computation.Charged.val_bind] at h
          cases hs : (restartPhase r o₁ o₂ tape s previous.tables j
              previous.bitCursor).val with
          | none => simp [hs] at h
          | some started =>
              simp only [hs, Arlib.Computation.Charged.val_bind] at h
              cases ho : (observePhase r o₁ o₂ tape s (ratPower s.ρ j).val
                  previous.currentWeights started).val with
              | none => simp [ho] at h
              | some observed =>
                  simp only [ho, Arlib.Computation.Charged.val_bind] at h
                  cases hf : (finishPhase s j previous.currentWeights observed).val with
                  | none => simp [hf] at h
                  | some finished =>
                      simp only [hf, Arlib.Computation.Charged.val_bind] at h
                      have hc := BoundedRunResourceEnvelope.observePhase_counts_le
                        r o₁ o₂ tape s (ratPower s.ρ j).val
                        previous.currentWeights started observed ho
                      have hn := FinishPhaseWeightsSize.finishPhase_weights_length_le
                        s j _ previous.currentWeights observed hc hw
                        finished.1 finished.2 hf
                      have hn' : ∀ index, binaryRatLength (finished.2 index) ≤
                          6 + (j + 1) * (n * n * (4 * (s.observations + 4))) := by
                        intro index
                        simpa only [Nat.add_mul, Nat.one_mul, Nat.add_assoc] using hn index
                      simp only [ratMul, successor, lessThan,
                        Arlib.Computation.Charged.val_opMany,
                        Arlib.Computation.Charged.val_op] at h
                      by_cases hu : j + 1 < s.L
                      · simp only [hu, decide_true, ite_true] at h
                        simp only [Arlib.Computation.Charged.val_bind,
                          Arlib.Computation.Charged.val_pure, Option.some.injEq] at h
                        subst current
                        refine ⟨hn', ?_⟩
                        intro phase index
                        simp only [learnedWeightWrite, Arlib.Computation.Charged.val_opMany]
                        split_ifs
                        · exact hn' index
                        · exact (ht phase index).trans (by
                            apply Nat.add_le_add_left
                            exact Nat.mul_le_mul_right _ (Nat.le_succ j))
                      · simp only [hu, decide_false, Bool.false_eq_true, ite_false] at h
                        simp only [Arlib.Computation.Charged.val_pure,
                          Option.some.injEq] at h
                        subst current
                        refine ⟨hn', ?_⟩
                        intro phase index
                        exact (ht phase index).trans (by
                          apply Nat.add_le_add_left
                          exact Nat.mul_le_mul_right _ (Nat.le_succ j))
