-- Prove2me | solution 1 for CountingMatroid.Analysis.BoundedRunPhase.phase_preserves_size
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T13:08:14.672492+00:00
-- url     : https://prove2.me/submissions/77074fe3-bf33-48c9-a02b-543b2ce56c3a

import Definitions.Def_CountingMatroidSupport_Computation_Charged
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension2
import Definitions.Def_CountingMatroidSupport_Computation_Cost
import Definitions.Def_CountingMatroidSupport_Computation_Dict
import Definitions.Def_CountingMatroidSupport_Computation_Heap
import Definitions.Def_CountingMatroidSupport_Computation_Machine
import Definitions.Def_CountingMatroidSupport_Computation_Num
import Definitions.Def_CountingMatroidSupport_Computation_Queue
import Definitions.Def_CountingMatroidSupport_Computation_Rand
import Definitions.Def_CountingMatroidSupport_Computation_Roster
import Definitions.Def_CountingMatroidSupport_Computation_Slot
import Definitions.Def_CountingMatroidSupport_Computation_Space
import Definitions.Def_CountingMatroidSupport_Computation_Std
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhase
import Definitions.Def_CountingMatroid_Analysis_EstimateMedianResource
import Definitions.Def_CountingMatroid_Analysis_RationalHeight
import Definitions.Def_CountingMatroid_Analysis_ScheduleOpeningCost
import Definitions.Def_CountingMatroid_Analysis_ScheduleThermalSetupCost
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
import Theorems.Thm_CountingMatroid_Analysis_BoundedRunResourceEnvelope_finishPhase_ratio_length_le
import Theorems.Thm_CountingMatroid_Analysis_BoundedRunResourceEnvelope_observePhase_counts_le
import Theorems.Thm_CountingMatroid_Analysis_BoundedRunResourceEnvelope_observePhase_height_le
import Theorems.Thm_CountingMatroid_Analysis_FinishPhaseWeightsSize_finishPhase_weights_length_le
import Theorems.Thm_CountingMatroid_Analysis_ScheduleOtherStepsEnvelope_binaryRatLength_mul_le

namespace CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
end CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
namespace CountingMatroid.Analysis.LeastHalvingsCost
end CountingMatroid.Analysis.LeastHalvingsCost
namespace CountingMatroid.Analysis
end CountingMatroid.Analysis
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
namespace CountingMatroid.Analysis.BoundedRunPhase
end CountingMatroid.Analysis.BoundedRunPhase
namespace CountingMatroid.Analysis.FinishPhaseWeightsSize
end CountingMatroid.Analysis.FinishPhaseWeightsSize
namespace CountingMatroid.Analysis.BoundedRunResourceEnvelope
end CountingMatroid.Analysis.BoundedRunResourceEnvelope
section


set_option autoImplicit false

namespace CountingMatroid.Analysis.RationalHeight
open CountingMatroid.Model





/-- INTERNAL: Two component lengths bound the rational encoding length. -/
theorem binaryRatLength_le_height (q : ℚ) :
    binaryRatLength q ≤ 2 * rationalHeight q + 2 := by
  unfold rationalHeight binaryRatLength binaryNatLength
  omega




end CountingMatroid.Analysis.RationalHeight

end
/-!
One bounded phase preserves the rational-size invariant for current weights,
stored tables, and the accumulated product. Abort branches satisfy the invariant
vacuously. Successful phases use the observation count and accumulator-height
bounds from `PhaseResourcePrimitives` and the multiplier scan bound from
`FinishPhaseWeightsSize`; the resulting ratio fits one phase increment.
-/

set_option autoImplicit false
namespace CountingMatroid.Analysis.BoundedRunPhase
end CountingMatroid.Analysis.BoundedRunPhase
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.BoundedRunPhase
open CountingMatroid.Model CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines CountingMatroid.Program

/-- INTERNAL: A successful phase grows every rational-size budget by at most
one phase increment; aborts preserve the invariant vacuously. This is a
value-only statement, independent of the charge paid to reach that value.
TEXLINE: main.tex:1356-1390 -/
theorem solution {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (hρ : 0 ≤ s.ρ)
    (j : ℕ) (hj : j < s.L) (acc : Option (AnnealingCursor n))
    (hacc : PhaseSizeInvariant (runSize n s) j acc) :
    PhaseSizeInvariant (runSize n s) (j + 1)
      (boundedRunPhase r o₁ o₂ tape s j acc).val := by
  cases acc with
  | none => simp [boundedRunPhase, PhaseSizeInvariant]
  | some current =>
      intro next hnext
      dsimp [boundedRunPhase] at hnext
      cases hstarted : (restartPhase r o₁ o₂ tape s current.tables j
        current.bitCursor).val with
      | none => simp [hstarted] at hnext
      | some started =>
          simp only [hstarted, Arlib.Computation.Charged.val_bind] at hnext
          cases hobserved : (observePhase r o₁ o₂ tape s
            (ratPower s.ρ j).val current.currentWeights started).val with
          | none => simp [hobserved] at hnext
          | some observed =>
              simp only [hobserved, Arlib.Computation.Charged.val_bind] at hnext
              cases hfinished : (finishPhase s j current.currentWeights observed).val with
              | none => simp [hfinished] at hnext
              | some finished =>
                  simp only [hfinished, Arlib.Computation.Charged.val_bind] at hnext
                  let S := runSize n s
                  have hS : 2 ≤ S := by dsimp [S, runSize]; omega
                  have hn : n ≤ S := by dsimp [S, runSize]; omega
                  have ho : s.observations ≤ S := by dsimp [S, runSize]; omega
                  have hinc : n * n * (4 * (s.observations + 4)) ≤ S ^ 10 := by
                    have hn2 : n * n ≤ S * S := Nat.mul_le_mul hn hn
                    have hd : 4 * (s.observations + 4) ≤ 20 * S := by omega
                    have hm := Nat.mul_le_mul hn2 hd
                    have hp : 20 ≤ S ^ 7 := by
                      have hp := Nat.pow_le_pow_left hS 7
                      norm_num at hp
                      omega
                    have hb := Nat.mul_le_mul_left (S ^ 3) hp
                    calc
                      n * n * (4 * (s.observations + 4)) ≤ S * S * (20 * S) := hm
                      _ = S ^ 3 * 20 := by ring
                      _ ≤ S ^ 3 * S ^ 7 := hb
                      _ = S ^ 10 := by rw [← pow_add]
                  suffices hcontracts :
                      (∀ kind, observed.counts kind ≤ s.observations) ∧
                      binaryRatLength finished.1 ≤ S ^ 10 by
                    obtain ⟨hw, ht, hp⟩ := hacc current rfl
                    have hweights := FinishPhaseWeightsSize.finishPhase_weights_length_le
                      s j ((j + 1) * S ^ 10) current.currentWeights observed
                      hcontracts.1 hw finished.1 finished.2 hfinished
                    have hwnew (index) : binaryRatLength (finished.2 index) ≤
                        (j + 1 + 1) * S ^ 10 := by
                      have := hweights index
                      nlinarith
                    have hproduct := ScheduleOtherStepsEnvelope.binaryRatLength_mul_le
                      current.product finished.1
                    have hpnew : binaryRatLength (current.product * finished.1) ≤
                        (j + 1 + 1) * S ^ 10 := by
                      have := hcontracts.2
                      dsimp [S] at *
                      nlinarith
                    simp only [ratMul, successor, lessThan,
                      Arlib.Computation.Charged.val_opMany,
                      Arlib.Computation.Charged.val_op] at hnext
                    by_cases hu : j + 1 < s.L
                    · simp only [hu, decide_true, ite_true] at hnext
                      simp only [Arlib.Computation.Charged.val_bind,
                        Arlib.Computation.Charged.val_pure, Option.some.injEq] at hnext
                      subst next
                      refine ⟨hwnew, ?_, hpnew⟩
                      intro phase index
                      simp only [learnedWeightWrite, Arlib.Computation.Charged.val_opMany]
                      split_ifs
                      · exact hwnew index
                      · have := ht phase index
                        dsimp [S] at *
                        nlinarith
                    · simp only [hu, decide_false, Bool.false_eq_true, ite_false] at hnext
                      simp only [Arlib.Computation.Charged.val_pure, Option.some.injEq] at hnext
                      subst next
                      refine ⟨hwnew, ?_, hpnew⟩
                      intro phase index
                      have := ht phase index
                      dsimp [S] at *
                      nlinarith
                  have hc := BoundedRunResourceEnvelope.observePhase_counts_le
                    r o₁ o₂ tape s (ratPower s.ρ j).val
                    current.currentWeights started observed hobserved
                  refine ⟨hc, ?_⟩
                  have hh := BoundedRunResourceEnvelope.observePhase_height_le
                    r o₁ o₂ tape s (ratPower s.ρ j).val
                    current.currentWeights started observed hobserved
                  have hl := RationalHeight.binaryRatLength_le_height observed.numeratorSum
                  have hr := BoundedRunResourceEnvelope.finishPhase_ratio_length_le
                    s j current.currentWeights observed (hc .transversal)
                    finished.1 finished.2 hfinished
                  have hρlen : binaryRatLength s.ρ ≤ S := by
                    dsimp [S, runSize]; omega
                  have hone : binaryRatLength 1 = 4 := by
                    norm_num [binaryRatLength, binaryNatLength, Nat.log2_eq_log_two]
                  rw [hone] at hh
                  have hnr : n * binaryRatLength s.ρ ≤ S * S :=
                    Nat.mul_le_mul hn hρlen
                  have hob : s.observations * (5 + n * binaryRatLength s.ρ) ≤
                      S * (5 + S * S) :=
                    Nat.mul_le_mul ho (Nat.add_le_add_left hnr 5)
                  have hratio : binaryRatLength finished.1 ≤ 16 + 13 * S + 2 * S ^ 3 := by
                    nlinarith
                  have hcube : S ≤ S ^ 3 := le_self_pow (by omega) (by decide)
                  have hlarge : 31 ≤ S ^ 7 := by
                    have hpower := Nat.pow_le_pow_left hS 7
                    norm_num at hpower
                    omega
                  calc
                    binaryRatLength finished.1 ≤ 16 + 13 * S + 2 * S ^ 3 := hratio
                    _ ≤ S ^ 3 * 31 := by nlinarith
                    _ ≤ S ^ 3 * S ^ 7 := Nat.mul_le_mul_left _ hlarge
                    _ = S ^ 10 := by rw [← pow_add]
