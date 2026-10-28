-- Prove2me | solution 1 for CountingMatroid.Analysis.BoundedRunOtherSteps.phaseFold_work_and_size
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:37:55.562663+00:00
-- url     : https://prove2.me/submissions/bd16574a-e99a-43fe-985a-7cb25abcebe2

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
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhaseWork
import Definitions.Def_CountingMatroid_Analysis_EstimateMedianResource
import Definitions.Def_CountingMatroid_Analysis_FinishPhaseWork
import Definitions.Def_CountingMatroid_Analysis_ObservePhaseWork
import Definitions.Def_CountingMatroid_Analysis_PhaseChainWork
import Definitions.Def_CountingMatroid_Analysis_PhaseResourcePrimitives
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
import Theorems.Thm_CountingMatroid_Analysis_BoundedRunPhase_phase_otherSteps_le
import Theorems.Thm_CountingMatroid_Analysis_BoundedRunPhase_phase_preserves_size

namespace CountingMatroid.Analysis.BoundedRunOtherSteps
end CountingMatroid.Analysis.BoundedRunOtherSteps
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
namespace CountingMatroid.Analysis.RestartPhaseWork
end CountingMatroid.Analysis.RestartPhaseWork
namespace CountingMatroid.Analysis.BoundedRunPhase
end CountingMatroid.Analysis.BoundedRunPhase
namespace CountingMatroid.Analysis.FinishPhaseWeightsSize
end CountingMatroid.Analysis.FinishPhaseWeightsSize
set_option autoImplicit false

/-!
The bounded-run nonoracle-work envelope is reduced to two single-phase
obligations: `phase_preserves_size` and `phase_otherSteps_le`. Their files
record the remaining multiplier-size and abort-path work proofs.

This module combines those statements by induction over the actual indexed
phase loop, bounds initialization, and proves the final-scaling work bound.
The full envelope is conditional on those two open child obligations; it is
not yet a completed resource proof. Existing power/count/height support is
still downstream in `BoundedRunResourceEnvelope` and needs upstream extraction
for use in the child proofs.
-/

namespace CountingMatroid.Analysis.BoundedRunOtherSteps
end CountingMatroid.Analysis.BoundedRunOtherSteps
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.BoundedRunOtherSteps
open CountingMatroid.Model
open CountingMatroid.Model.Subroutines

open CountingMatroid.Model.Operations CountingMatroid.Program
open CountingMatroid.Analysis.BoundedRunPhase
open CountingMatroid.Analysis.ResourceBound

/-- INTERNAL: Iterate the one-phase size invariant and cost bound together.
Keeping the phase index in the induction makes the cost hypothesis apply only
to reachable bounded-size cursors, including the absorbing aborted state.
TEXLINE: main.tex:1356-1440 -/
theorem solution {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool) (s : AnnealingSchedule)
    (hρ : 0 ≤ s.ρ) (k j : ℕ) (hj : j + k ≤ s.L)
    (acc : Option (AnnealingCursor n))
    (hacc : PhaseSizeInvariant (runSize n s) j acc) :
    let scan := Arlib.Computation.Charged.foldl
      (fun current index => boundedRunPhase r o₁ o₂ tape s index current)
      (List.range' j k) acc
    otherSteps scan ≤ k * (runSize n s) ^ 40 ∧
      PhaseSizeInvariant (runSize n s) (j + k) scan.val := by
  dsimp only
  induction k generalizing j acc with
  | zero => simpa [otherSteps] using hacc
  | succ k ih =>
      rw [List.range'_succ]
      change otherSteps (boundedRunPhase r o₁ o₂ tape s j acc >>= fun next =>
        Arlib.Computation.Charged.foldl
          (fun current index => boundedRunPhase r o₁ o₂ tape s index current)
          (List.range' (j + 1) k) next) ≤ _ ∧ _
      rw [otherSteps_bind]
      have hstep := phase_otherSteps_le r o₁ o₂ tape s hρ j (by omega) acc hacc
      have hnext := phase_preserves_size r o₁ o₂ tape s hρ j (by omega) acc hacc
      have htail := ih (j + 1) (by omega)
        (boundedRunPhase r o₁ o₂ tape s j acc).val hnext
      constructor
      · simpa [Nat.succ_mul, Nat.add_comm] using Nat.add_le_add hstep htail.1
      · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail.2
