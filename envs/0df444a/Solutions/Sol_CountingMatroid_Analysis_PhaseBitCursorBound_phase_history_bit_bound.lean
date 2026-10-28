-- Prove2me | solution 1 for CountingMatroid.Analysis.PhaseBitCursorBound.phase_history_bit_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:16:19.199278+00:00
-- url     : https://prove2.me/submissions/fe58d282-1753-4293-a1d9-6ec2f48de518

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
import Definitions.Def_CountingMatroid_Analysis_BoundedUniformReplay
import Definitions.Def_CountingMatroid_Analysis_ChainDrawSiteReplay
import Definitions.Def_CountingMatroid_Analysis_ChainStepIntervalReplay
import Definitions.Def_CountingMatroid_Analysis_EstimateMedianResource
import Definitions.Def_CountingMatroid_Analysis_FirstPhaseFailure
import Definitions.Def_CountingMatroid_Analysis_PhaseChainWork
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
import Mathlib.Data.List.OfFn
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
import Theorems.Thm_CountingMatroid_Analysis_BoundedRunResourceEnvelope_ratPower_binary_length_le
import Theorems.Thm_CountingMatroid_Analysis_PhaseBitCursorBound_observe_phase_bit_bound
import Theorems.Thm_CountingMatroid_Analysis_PhaseBitCursorBound_restart_phase_bit_bound
import Theorems.Thm_CountingMatroid_Analysis_PhaseHistoryMultiplierLength_phase_history_multiplier_length_le

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
namespace CountingMatroid.Analysis.PhaseBitCursorBound
end CountingMatroid.Analysis.PhaseBitCursorBound
namespace CountingMatroid.Analysis.InitialRestartLaw
end CountingMatroid.Analysis.InitialRestartLaw
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
namespace CountingMatroid.Analysis.ChainStepBitBound
end CountingMatroid.Analysis.ChainStepBitBound
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
set_option backward.isDefEq.respectTransparency false

namespace CountingMatroid.Analysis.PhaseBitCursorBound
end CountingMatroid.Analysis.PhaseBitCursorBound
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.PhaseBitCursorBound

open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program
open CountingMatroid.Analysis.ChainStepBitBound
open CountingMatroid.Analysis.BoundedRunResourceEnvelope

/-- INTERNAL: Sum restart and observation budgets across the actual history,
using the additive bound on its current and learned multipliers.
TEXLINE: main.tex:1356-1390,1392-1421 -/
theorem solution {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool)
    (s : AnnealingSchedule) (j K : ℕ) (hj : j ≤ s.L)
    (hq : binaryRatLength 1 + n * (binaryRatLength 1 + s.L * binaryRatLength s.ρ) ≤ K)
    (hw : 6 + s.L * (n * n * (4 * (s.observations + 4))) ≤ K)
    (current : AnnealingCursor n)
    (h : BoundedRunPhaseHistory.phaseHistory r o₁ o₂ tape s j = some current) :
    current.bitCursor ≤ j *
      (n + (s.restartCap + s.observations) * (1 + 3 * s.drawTrials * (4 * K + n + 1))) := by
  induction j generalizing current with
  | zero =>
      have he : BoundedRunPhaseHistory.initialCursor n s = current := Option.some.inj h
      subst current
      simp [BoundedRunPhaseHistory.initialCursor]
  | succ j ih =>
      rw [BoundedRunPhaseHistory.phaseHistory_succ] at h
      cases hp : BoundedRunPhaseHistory.phaseHistory r o₁ o₂ tape s j with
      | none => simp [hp, BoundedRunPhase.boundedRunPhase] at h
      | some previous =>
          rw [hp] at h
          have hprevious := ih (by omega) previous hp
          have hsize := PhaseHistoryMultiplierLength.phase_history_multiplier_length_le
            r o₁ o₂ tape s j previous hp
          have htable : ∀ phase i, binaryRatLength (previous.tables phase i) ≤ K := by
            intro phase i
            apply (hsize.2 phase i).trans
            exact (Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega : j ≤ s.L)) _).trans hw
          have hweights : ∀ i, binaryRatLength (previous.currentWeights i) ≤ K := by
            intro i
            apply (hsize.1 i).trans
            exact (Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega : j ≤ s.L)) _).trans hw
          unfold BoundedRunPhase.boundedRunPhase at h
          simp only [Arlib.Computation.Charged.val_bind] at h
          cases hs : (restartPhase r o₁ o₂ tape s previous.tables j previous.bitCursor).val with
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
                      have hcursor : current.bitCursor = observed.bitCursor := by
                        by_cases hu : (lessThan (successor j).val s.L).val = true
                        · rw [if_pos hu] at h
                          simp only [Arlib.Computation.Charged.val_bind] at h
                          exact (congrArg AnnealingCursor.bitCursor (Option.some.inj h)).symm
                        · rw [if_neg hu] at h
                          exact (congrArg AnnealingCursor.bitCursor (Option.some.inj h)).symm
                      have hqj : binaryRatLength 1 + n * binaryRatLength (ratPower s.ρ j).val ≤ K := by
                        have hl := ratPower_binary_length_le s.ρ j
                        have hm := Nat.mul_le_mul_right (binaryRatLength s.ρ) (show j ≤ s.L by omega)
                        exact (Nat.add_le_add_left (Nat.mul_le_mul_left n
                          (hl.trans (Nat.add_le_add_left hm _))) _).trans hq
                      have hrs := restart_phase_bit_bound r o₁ o₂ tape s previous.tables
                        j previous.bitCursor K (by omega) hq htable started hs
                      have hob := observe_phase_bit_bound r o₁ o₂ tape s (ratPower s.ρ j).val
                        previous.currentWeights started K hqj hweights observed ho
                      let C := 1 + 3 * s.drawTrials * (4 * K + n + 1)
                      change previous.bitCursor ≤ j * (n + (s.restartCap + s.observations) * C) at hprevious
                      change started.2 ≤ previous.bitCursor + n + s.restartCap * C at hrs
                      change observed.bitCursor ≤ started.2 + s.observations * C at hob
                      change current.bitCursor ≤ (j + 1) * (n + (s.restartCap + s.observations) * C)
                      rw [hcursor]
                      calc
                        observed.bitCursor ≤ started.2 + s.observations * C := hob
                        _ ≤ previous.bitCursor + n + s.restartCap * C + s.observations * C :=
                          Nat.add_le_add_right hrs _
                        _ ≤ j * (n + (s.restartCap + s.observations) * C) + n +
                            s.restartCap * C + s.observations * C := by omega
                        _ = (j + 1) * (n + (s.restartCap + s.observations) * C) := by ring
