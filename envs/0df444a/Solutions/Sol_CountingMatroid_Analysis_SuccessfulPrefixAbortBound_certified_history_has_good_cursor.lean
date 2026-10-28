-- Prove2me | solution 1 for CountingMatroid.Analysis.SuccessfulPrefixAbortBound.certified_history_has_good_cursor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:39:37.570907+00:00
-- url     : https://prove2.me/submissions/eb0c41ce-2c4e-49f2-b409-713cbc3db437

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
import Definitions.Def_CountingMatroid_Analysis_AnnealingPartitionDrift
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhase
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhaseHistory
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhaseWork
import Definitions.Def_CountingMatroid_Analysis_DefectPartitionPositive
import Definitions.Def_CountingMatroid_Analysis_EmpiricalPhaseCertificate
import Definitions.Def_CountingMatroid_Analysis_EstimateMedianResource
import Definitions.Def_CountingMatroid_Analysis_FinishPhaseEmpiricalUpdate
import Definitions.Def_CountingMatroid_Analysis_FinishPhaseWork
import Definitions.Def_CountingMatroid_Analysis_FirstPhaseFailure
import Definitions.Def_CountingMatroid_Analysis_InitialMultipliersGood
import Definitions.Def_CountingMatroid_Analysis_ObservePhaseWork
import Definitions.Def_CountingMatroid_Analysis_PhaseChainWork
import Definitions.Def_CountingMatroid_Analysis_PhaseMeanCertificate
import Definitions.Def_CountingMatroid_Analysis_PhaseObservationExperiment
import Definitions.Def_CountingMatroid_Analysis_PhaseResourcePrimitives
import Definitions.Def_CountingMatroid_Analysis_RationalHeight
import Definitions.Def_CountingMatroid_Analysis_RelativeObservationBounds
import Definitions.Def_CountingMatroid_Analysis_ScheduleConfidence
import Definitions.Def_CountingMatroid_Analysis_ScheduleOpeningCost
import Definitions.Def_CountingMatroid_Analysis_ScheduleThermalSetupCost
import Definitions.Def_CountingMatroid_Analysis_StationaryMeanIdentities
import Definitions.Def_CountingMatroid_Analysis_TransversalClassPartition
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
import Mathlib.Algebra.Order.Ring.Pow
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
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF
import Theorems.Thm_CountingMatroid_Analysis_InitialMultipliersGood_defect_partition_one

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
namespace CountingMatroid.Analysis.SuccessfulPrefixAbortBound
end CountingMatroid.Analysis.SuccessfulPrefixAbortBound
namespace CountingMatroid.Analysis.BoundedRunResourceEnvelope
end CountingMatroid.Analysis.BoundedRunResourceEnvelope
namespace CountingMatroid.Analysis.BoundedRunOtherSteps
end CountingMatroid.Analysis.BoundedRunOtherSteps
namespace CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
end CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
namespace CountingMatroid.Analysis.LeastHalvingsCost
end CountingMatroid.Analysis.LeastHalvingsCost
namespace CountingMatroid.Analysis
end CountingMatroid.Analysis
namespace CountingMatroid.Analysis.RestartPhaseWork
end CountingMatroid.Analysis.RestartPhaseWork
namespace CountingMatroid.Analysis.BoundedRunPhase
end CountingMatroid.Analysis.BoundedRunPhase
namespace CountingMatroid.Analysis.FinishPhaseWeightsSize
end CountingMatroid.Analysis.FinishPhaseWeightsSize
namespace CountingMatroid.Analysis.BoundedRunOracleCalls
end CountingMatroid.Analysis.BoundedRunOracleCalls
namespace CountingMatroid.Analysis.ResourceBound
end CountingMatroid.Analysis.ResourceBound
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

section


set_option autoImplicit false

namespace CountingMatroid.Analysis.InitialMultipliersGood

open CountingMatroid.Model CountingMatroid.Analysis
open CountingMatroid.Program CountingMatroid.Model.Operations

































/-- PAPER: main.tex:1148-1151
The initial multiplier four is ideal whenever an ordered defect type exists.
The statement includes the vacuous defect families at `n = 0` and `n = 1`.
Its counting proof must characterize the executable classifier's defect fiber,
rather than assume an independent mathematical state classifier. -/
theorem initial_ideal_multiplier {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (index : DefectIndex n) :
    TransversalPartition.partitionSum r o₁ o₂ 1 /
      FirstPhaseFailure.defectPartition r o₁ o₂ 1 index = 4 := by
  have hn : 2 ≤ n := by
    by_contra h
    apply index.distinct
    apply Fin.ext
    omega
  rw [defect_partition_one]
  have hC : TransversalPartition.partitionSum r o₁ o₂ 1 = (2 : ℚ) ^ n := by
    simp [TransversalPartition.partitionSum]
  rw [hC, show n = (n - 2) + 2 by omega, pow_add]
  norm_num

end CountingMatroid.Analysis.InitialMultipliersGood

end
set_option autoImplicit false

namespace CountingMatroid.Analysis.SuccessfulPrefixAbortBound
end CountingMatroid.Analysis.SuccessfulPrefixAbortBound
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.SuccessfulPrefixAbortBound

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.PhaseObservationExperiment

/-- INTERNAL: Earlier actual phase certificates supply a reached good cursor
on the same tape, without any replay or tape-coverage assumption.
TEXLINE: main.tex:1207-1212 -/
theorem solution {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (p : InputParams) (tape : ℕ → Bool)
    (j : ℕ) (hj : j < (CountingMatroid.Interface.Pseudocode.setup n p).L)
    (hprevious : ∀ a < j, FirstPhaseFailure.CertifiedPhase r o₁ o₂ tape
      (CountingMatroid.Interface.Pseudocode.setup n p) a) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    ∃ current : AnnealingCursor n,
      BoundedRunPhaseHistory.phaseHistory r o₁ o₂ tape s j = some current ∧
      FirstPhaseFailure.GoodStoredMultipliers r o₁ o₂ s j current := by
  let s := CountingMatroid.Interface.Pseudocode.setup n p
  cases j with
  | zero =>
      refine ⟨BoundedRunPhaseHistory.initialCursor n s, rfl, ?_⟩
      simp [FirstPhaseFailure.GoodStoredMultipliers,
        BoundedRunPhaseHistory.initialCursor,
        CountingMatroid.Model.Operations.initialWeights,
        CountingMatroid.Model.Operations.allocateLearnedWeights,
        InitialMultipliersGood.initial_ideal_multiplier]
  | succ a =>
      obtain ⟨ratio, _, _, previous, next, hpreviousCursor, hnext, _, _, hgood⟩ :=
        hprevious a (Nat.lt_succ_self a)
      refine ⟨next, ?_, hgood hj⟩
      rw [BoundedRunPhaseHistory.phaseHistory_succ,
        show BoundedRunPhaseHistory.phaseHistory r o₁ o₂ tape s a =
          some previous from hpreviousCursor]
      exact hnext
