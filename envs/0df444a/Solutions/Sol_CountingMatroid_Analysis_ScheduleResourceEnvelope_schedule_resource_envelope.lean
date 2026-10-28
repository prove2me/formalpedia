-- Prove2me | solution 1 for CountingMatroid.Analysis.ScheduleResourceEnvelope.schedule_resource_envelope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:07:17.365542+00:00
-- url     : https://prove2.me/submissions/aa0bdb54-0ed4-4069-9710-776d509461a8

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
import Definitions.Def_CountingMatroid_Analysis_ScheduleDrawTrialsBridge
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
import Theorems.Thm_CountingMatroid_Analysis_ScheduleCostEnvelope_schedule_oracleCalls_zero
import Theorems.Thm_CountingMatroid_Analysis_ScheduleOtherStepsEnvelope_schedule_otherSteps_envelope
import Theorems.Thm_CountingMatroid_Analysis_ScheduleResourceEnvelope_schedule_rho_nonneg
import Theorems.Thm_CountingMatroid_Analysis_ScheduleValueEnvelope_schedule_value_envelope

namespace CountingMatroid.Analysis.ScheduleCostEnvelope
end CountingMatroid.Analysis.ScheduleCostEnvelope
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
namespace CountingMatroid.Analysis.ScheduleResourceEnvelope
end CountingMatroid.Analysis.ScheduleResourceEnvelope
namespace CountingMatroid.Analysis.ScheduleValueEnvelope
end CountingMatroid.Analysis.ScheduleValueEnvelope
namespace CountingMatroid.Analysis.BoundedRunResourceEnvelope
end CountingMatroid.Analysis.BoundedRunResourceEnvelope
namespace CountingMatroid.Analysis.BoundedRunOtherSteps
end CountingMatroid.Analysis.BoundedRunOtherSteps
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
set_option maxHeartbeats 1000000

namespace CountingMatroid.Analysis.ScheduleCostEnvelope

open CountingMatroid.Model
open CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines
















/-- INTERNAL: The charged construction of the schedule has polynomial cost
in the encoded input size. This is the cost part of the schedule resource envelope.
TEXLINE: main.tex:1348-1358 -/
theorem schedule_cost_envelope :
    ∃ (C degree : ℕ), ∀ (n r : ℕ) (p : InputParams),
      let inputSize := n + binaryInputLength n r p + Nat.ceil p.ε⁻¹ +
        binaryNatLength (Nat.ceil p.δ⁻¹) + 1
      let schedule := CountingMatroid.Program.schedule n p
      oracleCalls schedule ≤ C * inputSize ^ degree ∧
      otherSteps schedule ≤ C * inputSize ^ degree := by
  obtain ⟨C, degree, hother⟩ :=
    ScheduleOtherStepsEnvelope.schedule_otherSteps_envelope
  refine ⟨C, degree, ?_⟩
  intro n r p
  exact ⟨by simp [schedule_oracleCalls_zero], hother n r p⟩

end CountingMatroid.Analysis.ScheduleCostEnvelope

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r10 · partial · proved zero oracle cost and reduced the target to the separate nonoracle schedule charge bound; scheduler handoff request was refused by the shell policy.
* r9 · open · zero oracle charges proved for bounded searches and natural powers; the full charged bound needs rational encoding estimates.
-/

end
set_option autoImplicit false

namespace CountingMatroid.Analysis.ScheduleResourceEnvelope
end CountingMatroid.Analysis.ScheduleResourceEnvelope
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ScheduleResourceEnvelope

open CountingMatroid.Model
open CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines

/-- INTERNAL: The charged schedule construction produces polynomially bounded
loop caps and a nonnegative annealing base. This is independent of the phase
state and of the median computation.
TEXLINE: main.tex:1348-1356, 1397-1421 -/
theorem solution :
    ∃ (C degree : ℕ), ∀ (n r : ℕ) (p : InputParams),
      let inputSize := n + binaryInputLength n r p + Nat.ceil p.ε⁻¹ +
        binaryNatLength (Nat.ceil p.δ⁻¹) + 1
      let schedule := CountingMatroid.Program.schedule n p
      let s := schedule.val
      0 ≤ s.ρ ∧
      n + s.L + s.τ + s.restartCap + s.observations + s.drawTrials +
        binaryRatLength s.ρ + s.repetitions + 1 ≤ C * inputSize ^ degree ∧
      oracleCalls schedule ≤ C * inputSize ^ degree ∧
      otherSteps schedule ≤ C * inputSize ^ degree := by
  -- The sign condition is discharged directly from the concrete charged schedule.
  -- The remaining obligation is only the common polynomial envelope for values
  -- and charged arithmetic. In particular it does not need a separate claim
  -- that either bounded search reaches its mathematical threshold.
  have hpoly :
      ∃ (C degree : ℕ), ∀ (n r : ℕ) (p : InputParams),
        let inputSize := n + binaryInputLength n r p + Nat.ceil p.ε⁻¹ +
          binaryNatLength (Nat.ceil p.δ⁻¹) + 1
        let schedule := CountingMatroid.Program.schedule n p
        let s := schedule.val
        n + s.L + s.τ + s.restartCap + s.observations + s.drawTrials +
          binaryRatLength s.ρ + s.repetitions + 1 ≤ C * inputSize ^ degree ∧
        oracleCalls schedule ≤ C * inputSize ^ degree ∧
        otherSteps schedule ≤ C * inputSize ^ degree := by
    obtain ⟨Cv, dv, hv⟩ := ScheduleValueEnvelope.schedule_value_envelope
    obtain ⟨Cc, dc, hc⟩ := ScheduleCostEnvelope.schedule_cost_envelope
    refine ⟨Cv + Cc, max dv dc, ?_⟩
    intro n r p
    let N := n + binaryInputLength n r p + Nat.ceil p.ε⁻¹ +
      binaryNatLength (Nat.ceil p.δ⁻¹) + 1
    have hN : 0 < N := by dsimp [N]; omega
    have hpowV : N ^ dv ≤ N ^ max dv dc :=
      Nat.pow_le_pow_right hN (le_max_left _ _)
    have hpowC : N ^ dc ≤ N ^ max dv dc :=
      Nat.pow_le_pow_right hN (le_max_right _ _)
    have hCv : Cv ≤ Cv + Cc := by omega
    have hCc : Cc ≤ Cv + Cc := by omega
    have hV : Cv * N ^ dv ≤ (Cv + Cc) * N ^ max dv dc :=
      le_trans (Nat.mul_le_mul_left Cv hpowV)
        (Nat.mul_le_mul_right _ hCv)
    have hC : Cc * N ^ dc ≤ (Cv + Cc) * N ^ max dv dc :=
      le_trans (Nat.mul_le_mul_left Cc hpowC)
        (Nat.mul_le_mul_right _ hCc)
    have hv' := hv n r p
    have hc' := hc n r p
    dsimp at hv' hc' ⊢
    exact ⟨le_trans hv' hV, le_trans hc'.1 hC, le_trans hc'.2 hC⟩
  obtain ⟨C, degree, hpoly⟩ := hpoly
  refine ⟨C, degree, ?_⟩
  intro n r p
  exact ⟨schedule_rho_nonneg n p, hpoly n r p⟩
