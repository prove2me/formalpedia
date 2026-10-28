-- Prove2me | solution 1 for CountingMatroid.Analysis.ObservationRoundDrawSiteCovered.observation_round_draw_site_covered
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:27:37.712068+00:00
-- url     : https://prove2.me/submissions/1746818b-6fec-4f56-8ab5-aa853901721e

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
import Definitions.Def_CountingMatroid_Analysis_BoundedUniformAbortMass
import Definitions.Def_CountingMatroid_Analysis_BoundedUniformReplay
import Definitions.Def_CountingMatroid_Analysis_ChainDrawSiteReplay
import Definitions.Def_CountingMatroid_Analysis_ChainStepIntervalReplay
import Definitions.Def_CountingMatroid_Analysis_DefectPartitionPositive
import Definitions.Def_CountingMatroid_Analysis_EmpiricalPhaseCertificate
import Definitions.Def_CountingMatroid_Analysis_EstimateMedianResource
import Definitions.Def_CountingMatroid_Analysis_FinishPhaseEmpiricalUpdate
import Definitions.Def_CountingMatroid_Analysis_FinishPhaseWork
import Definitions.Def_CountingMatroid_Analysis_FirstPhaseFailure
import Definitions.Def_CountingMatroid_Analysis_InitialMultipliersGood
import Definitions.Def_CountingMatroid_Analysis_ObservationRoundDrawSiteCovered
import Definitions.Def_CountingMatroid_Analysis_ObservationRoundDrawSites
import Definitions.Def_CountingMatroid_Analysis_ObservePhaseWork
import Definitions.Def_CountingMatroid_Analysis_PhaseChainWork
import Definitions.Def_CountingMatroid_Analysis_PhaseMeanCertificate
import Definitions.Def_CountingMatroid_Analysis_PhaseObservationExperiment
import Definitions.Def_CountingMatroid_Analysis_PhaseResourcePrimitives
import Definitions.Def_CountingMatroid_Analysis_RationalHeight
import Definitions.Def_CountingMatroid_Analysis_RelativeObservationBounds
import Definitions.Def_CountingMatroid_Analysis_ScheduleConfidence
import Definitions.Def_CountingMatroid_Analysis_ScheduleDrawTrialsBridge
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
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Induction
import Mathlib.Data.List.Infix
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
import Theorems.Thm_CountingMatroid_Analysis_BoundedRunResourceEnvelope_ratPower_binary_length_le
import Theorems.Thm_CountingMatroid_Analysis_ChainStepBitBound_chain_draw_site_bit_bound
import Theorems.Thm_CountingMatroid_Analysis_ObservationRoundDrawSites_chainDrawSite_success_interval
import Theorems.Thm_CountingMatroid_Analysis_ObservePhaseIntervalReplay_observePhase_success_interval
import Theorems.Thm_CountingMatroid_Analysis_PhaseBitCursorBound_observe_phase_bit_bound
import Theorems.Thm_CountingMatroid_Analysis_PhaseBitCursorBound_phase_history_bit_bound
import Theorems.Thm_CountingMatroid_Analysis_PhaseBitCursorBound_restart_phase_bit_bound
import Theorems.Thm_CountingMatroid_Analysis_PhaseHistoryMultiplierLength_phase_history_multiplier_length_le
import Theorems.Thm_CountingMatroid_Analysis_RestartPhaseIntervalReplay_restartPhase_success_interval
import Theorems.Thm_CountingMatroid_Analysis_SinglePhaseIntervalReplay_single_phase_interval_replay
import Theorems.Thm_CountingMatroid_Analysis_SuccessfulPhaseReplay_successful_history_replay_of_phase_replay
import Theorems.Thm_CountingMatroid_Analysis_SuccessfulPrefixAbortBound_successful_prefix_has_good_cursor

namespace CountingMatroid.Analysis.PhaseBitCursorBound
end CountingMatroid.Analysis.PhaseBitCursorBound
namespace CountingMatroid.Analysis.InitialRestartLaw
end CountingMatroid.Analysis.InitialRestartLaw
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
namespace CountingMatroid.Analysis.ChainStepBitBound
end CountingMatroid.Analysis.ChainStepBitBound
namespace CountingMatroid.Analysis.SuccessfulPrefixAbortBound
end CountingMatroid.Analysis.SuccessfulPrefixAbortBound
namespace CountingMatroid.Analysis.BoundedRunResourceEnvelope
end CountingMatroid.Analysis.BoundedRunResourceEnvelope
namespace CountingMatroid.Analysis.BoundedRunOtherSteps
end CountingMatroid.Analysis.BoundedRunOtherSteps
namespace CountingMatroid.Analysis.RestartPhaseWork
end CountingMatroid.Analysis.RestartPhaseWork
namespace CountingMatroid.Analysis.BoundedRunPhase
end CountingMatroid.Analysis.BoundedRunPhase
namespace CountingMatroid.Analysis.BoundedRunOracleCalls
end CountingMatroid.Analysis.BoundedRunOracleCalls
namespace CountingMatroid.Analysis.ResourceBound
end CountingMatroid.Analysis.ResourceBound
namespace CountingMatroid.Analysis.ObservationRoundDrawSites
end CountingMatroid.Analysis.ObservationRoundDrawSites
namespace CountingMatroid.Analysis.ClassifiedStateSelection
end CountingMatroid.Analysis.ClassifiedStateSelection
namespace CountingMatroid.Analysis.FiniteObservationMarkov
end CountingMatroid.Analysis.FiniteObservationMarkov
namespace CountingMatroid.Analysis.FiniteTapePrefixBound
end CountingMatroid.Analysis.FiniteTapePrefixBound
namespace CountingMatroid.Analysis.SuccessfulPhaseReplay
end CountingMatroid.Analysis.SuccessfulPhaseReplay
namespace CountingMatroid.Analysis.SinglePhaseIntervalReplay
end CountingMatroid.Analysis.SinglePhaseIntervalReplay
namespace CountingMatroid.Analysis.RestartPhaseIntervalReplay
end CountingMatroid.Analysis.RestartPhaseIntervalReplay
namespace CountingMatroid.Analysis.TraceReturnIntervalReplay
end CountingMatroid.Analysis.TraceReturnIntervalReplay
namespace CountingMatroid.Analysis.ObservePhaseIntervalReplay
end CountingMatroid.Analysis.ObservePhaseIntervalReplay
namespace CountingMatroid.Analysis.ChainStepNoninvalid
end CountingMatroid.Analysis.ChainStepNoninvalid
namespace CountingMatroid.Analysis.RestartPhaseTransversal
end CountingMatroid.Analysis.RestartPhaseTransversal
namespace CountingMatroid.Analysis.ScheduleResourceEnvelope
end CountingMatroid.Analysis.ScheduleResourceEnvelope
namespace CountingMatroid.Analysis.ScheduleCostEnvelope
end CountingMatroid.Analysis.ScheduleCostEnvelope
namespace CountingMatroid.Analysis.ScheduleValueEnvelope
end CountingMatroid.Analysis.ScheduleValueEnvelope
section

set_option autoImplicit false
open CountingMatroid.Model
open CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines
namespace CountingMatroid.Analysis.ScheduleOtherStepsEnvelope



/-- INTERNAL: The source schedule is exactly its opening followed by its remainder.
TEXLINE: main.tex:1348-1358 -/
theorem schedule_split (n : ℕ) (p : InputParams) :
    CountingMatroid.Program.schedule n p = scheduleOpening n p >>= scheduleRemaining n p := by
  simp only [CountingMatroid.Program.schedule, scheduleOpening, scheduleRemaining, bind_assoc, pure_bind]
/-- INTERNAL: The opening computation produces the values used by the
remaining schedule operations. -/
theorem scheduleOpening_value (n : ℕ) (p : InputParams) :
    (scheduleOpening n p).val =
      ⟨(CountingMatroid.Program.leastHalvings (p.ε / 10)).val,
        1 - 1 / (2 * n : ℚ), 2 * n⟩ := by
  simp [scheduleOpening, ratDiv, ratSub, natMul, ratOfNat]







end CountingMatroid.Analysis.ScheduleOtherStepsEnvelope

end

section


set_option autoImplicit false

/-!
The quantitative finite-block obligation for the concrete observation draw
stopping maps. The bound must account for all earlier actual phase updates,
restart attempts, and k observations. The additive multiplier, draw, restart, observation, and actual-history
budgets are proved in the support modules. The target proof combines prefix
replay for the lower endpoint with the quartic bound for the full trial interval.
The generic observation-prefix bridge checks record-update projections before
instantiation with the concrete schedule, keeping the composed budget proof
small enough for kernel validation.
-/

namespace CountingMatroid.Analysis.ObservationRoundDrawSiteCovered

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.PhaseObservationExperiment
open CountingMatroid.Analysis.ObservationRoundDrawSites

/-- INTERNAL: Transfer a continuation's value property across charged sequencing. -/
private theorem bind_value_property {α β : Type}
    (c : Arlib.Computation.Charged Model.Operations.Op Model.Operations.Cell α)
    (f : α → Arlib.Computation.Charged Model.Operations.Op Model.Operations.Cell β)
    (P : β → Prop) (h : ∀ x, P (f x).val) : P (c >>= f).val := by
  simpa only [Arlib.Computation.Charged.val_bind] using h c.val





set_option backward.isDefEq.respectTransparency false in
/-- INTERNAL: The concrete annealing ratio has a ground-size encoding bound.
The matching fact in ScheduleValueEnvelope is private.
TEXLINE: main.tex:1382-1390 -/
private theorem setup_rho_length_bound (n : ℕ) (p : InputParams) (hn : 0 < n) :
    binaryRatLength (CountingMatroid.Interface.Pseudocode.setup n p).ρ ≤ 4 * n + 6 := by
  let q := (CountingMatroid.Interface.Pseudocode.setup n p).ρ
  have hremaining (head : ScheduleOtherStepsEnvelope.ScheduleOpeningResult) :
      (ScheduleOtherStepsEnvelope.scheduleRemaining n p head).val.ρ = head.rho := by
    change RhoProperty head.rho (ScheduleOtherStepsEnvelope.scheduleRemaining n p head).val
    unfold ScheduleOtherStepsEnvelope.scheduleRemaining
    dsimp only
    iterate 30
      apply bind_value_property
      intro
    rfl
  have hq : q = 1 - 1 / (2 * n : ℚ) := by
    change (CountingMatroid.Program.schedule n p).val.ρ = _
    rw [ScheduleOtherStepsEnvelope.schedule_split, Arlib.Computation.Charged.val_bind,
      hremaining, ScheduleOtherStepsEnvelope.scheduleOpening_value]
  have hden : q.den = 2 * n := by
    rw [hq]
    have hcast : (2 * n : ℚ) = ((2 * n : ℕ) : ℚ) := by norm_num [Nat.cast_mul]
    rw [hcast, one_div, show (1 : ℚ) = ((1 : ℕ) : ℚ) by norm_num,
      Rat.natCast_sub_den, Rat.inv_natCast_den_of_pos (by omega : 0 < 2 * n)]
  have hb := (AnnealingPartitionDrift.schedule_power_lower n p hn)
  have hnum0 : 0 ≤ q.num := Rat.num_nonneg.mpr hb.1.le
  have hnum1 : q.num ≤ (q.den : ℤ) := by
    have hunit : q ≤ 1 := hb.2.1
    rw [← q.num_div_den] at hunit
    have h : (q.num : ℚ) ≤ (q.den : ℚ) := by
      simpa using (div_le_iff₀ (by exact_mod_cast q.den_pos)).mp hunit
    exact_mod_cast h
  have hnum : q.num.natAbs ≤ q.den := by
    have h : (q.num.natAbs : ℤ) ≤ (q.den : ℤ) := by
      simpa [Int.natAbs_of_nonneg hnum0] using hnum1
    exact_mod_cast h
  have hnlog := Nat.log_le_self 2 q.num.natAbs
  have hdlog := Nat.log_le_self 2 q.den
  change binaryRatLength q ≤ _
  unfold binaryRatLength binaryNatLength
  simp only [← Nat.log2_eq_log_two] at hnlog hdlog
  omega

/-- INTERNAL: The fixed block's quartic width covers the additive history
multiplier budget and the acceptance-ratio denominator width.
TEXLINE: main.tex:1356-1390 -/
private theorem quartic_width_covers (n L N I rhoLength : ℕ)
    (hrho : rhoLength ≤ 4 * n + 6) :
    let K := 4 + n * (4 + L * rhoLength) + 6 + L * (n * n * (4 * (N + 4)))
    4 * K + n + 1 ≤ 1000000 * (L + 1) ^ 4 * (n + 1) ^ 4 *
      (N + 1) ^ 4 * (I + 1) ^ 4 := by
  let B := (L + 1) * (n + 1) ^ 2 * (N + 1)
  have hB : 1 ≤ B := by
    have hp : 0 < B := by dsimp [B]; positivity
    omega
  have hbase : (n + 1) ^ 2 ≤ B := by
    calc
      (n + 1) ^ 2 = 1 * (n + 1) ^ 2 * 1 := by ring
      _ ≤ (L + 1) * (n + 1) ^ 2 * (N + 1) := by gcongr <;> omega
  have hbaseL : (L + 1) * (n + 1) ^ 2 ≤ B := by
    calc
      (L + 1) * (n + 1) ^ 2 = ((L + 1) * (n + 1) ^ 2) * 1 := by ring
      _ ≤ ((L + 1) * (n + 1) ^ 2) * (N + 1) := by gcongr; omega
  have hnB : n ≤ B := (show n ≤ (n + 1) ^ 2 by nlinarith).trans hbase
  have hthermal : n * L * rhoLength ≤ 10 * B := by
    calc
      n * L * rhoLength ≤ (n + 1) * (L + 1) * (10 * (n + 1)) := by gcongr <;> omega
      _ = 10 * ((L + 1) * (n + 1) ^ 2) := by ring
      _ ≤ 10 * B := Nat.mul_le_mul_left 10 hbaseL
  have hupdate : L * (n * n * (4 * (N + 4))) ≤ 16 * B := by
    calc
      L * (n * n * (4 * (N + 4))) ≤
          (L + 1) * ((n + 1) * (n + 1) * (4 * (4 * (N + 1)))) := by gcongr <;> omega
      _ = 16 * B := by dsimp [B]; ring
  have hK : 4 + n * (4 + L * rhoLength) + 6 + L * (n * n * (4 * (N + 4))) ≤ 40 * B := by
    nlinarith only [hB, hnB, hthermal, hupdate]
  have hW : 4 * (4 + n * (4 + L * rhoLength) + 6 + L * (n * n * (4 * (N + 4)))) + n + 1 ≤ 162 * B := by
    omega
  have hBpow : B ≤ B ^ 2 := le_self_pow hB (by decide)
  have hwidth : B ^ 2 ≤ (L + 1) ^ 4 * (n + 1) ^ 4 * (N + 1) ^ 4 * (I + 1) ^ 4 := by
    calc
      B ^ 2 = (L + 1) ^ 2 * (n + 1) ^ 4 * (N + 1) ^ 2 * 1 := by dsimp [B]; ring
      _ ≤ (L + 1) ^ 4 * (n + 1) ^ 4 * (N + 1) ^ 4 * (I + 1) ^ 4 := by
        have hL : (L + 1) ^ 2 ≤ (L + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by decide)
        have hN : (N + 1) ^ 2 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by decide)
        have hI : 1 ≤ (I + 1) ^ 4 := by
          have hp : 0 < (I + 1) ^ 4 := by positivity
          omega
        exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hL (le_refl _)) hN) hI
  dsimp only
  apply hW.trans
  calc
    162 * B ≤ 1000000 * B ^ 2 := by nlinarith only [hBpow, hB]
    _ ≤ 1000000 * ((L + 1) ^ 4 * (n + 1) ^ 4 * (N + 1) ^ 4 * (I + 1) ^ 4) := Nat.mul_le_mul_left _ hwidth
    _ = _ := by ring

/-- INTERNAL: The final schedule constructor stores exactly the charged
three-draw allowance. TEXLINE: main.tex:1405-1408 -/
private theorem schedule_tail_draw_calls_eq (bε : ℕ) (rho : ℚ) (L : ℕ) (eta : ℚ)
    (tau restartCap observations : ℕ) (p : InputParams) :
    let s := (do
      let attemptsAndObservations ← Model.Operations.natAdd restartCap observations
      let threeL ← Model.Operations.natMul 3 L
      let drawCalls ← Model.Operations.natMul threeL attemptsAndObservations
      let drawTrials ← CountingMatroid.Program.leastDrawTrials drawCalls
      let bδ ← CountingMatroid.Program.leastHalvings p.δ
      let tenBδ ← Model.Operations.natMul 10 bδ
      let repetitions ← Model.Operations.successor tenBδ
      pure (AnnealingSchedule.mk bε rho L eta tau restartCap observations
        drawCalls drawTrials bδ repetitions) :
        Arlib.Computation.Charged Model.Operations.Op Model.Operations.Cell AnnealingSchedule).val
    s.drawCalls = 3 * s.L * (s.restartCap + s.observations) := by
  simp only [Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.val_pure,
    Model.Operations.natAdd, Model.Operations.natMul, Arlib.Computation.Charged.val_op]

set_option backward.isDefEq.respectTransparency false in
/-- INTERNAL: Peel schedule binds without expanding their expensive values.
TEXLINE: main.tex:1405-1408 -/
private theorem setup_draw_calls_eq (n : ℕ) (p : InputParams) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    s.drawCalls = 3 * s.L * (s.restartCap + s.observations) := by
  change DrawCallsProperty (CountingMatroid.Program.schedule n p).val
  unfold CountingMatroid.Program.schedule
  iterate 29
    apply bind_value_property
    intro
  exact schedule_tail_draw_calls_eq _ _ _ _ _ _ _ p

/-- INTERNAL: Convert a phase-linear chain budget into the block's
three-draw-call allowance without unfolding the concrete schedule. -/
private theorem draw_budget_arithmetic (n L A D W₀ W : ℕ) (hW : W₀ ≤ W) :
    L * (n + A * (1 + 3 * D * W₀)) ≤ n * L + 3 * L * A * (1 + D * W) + 10 := by
  have hm := Nat.mul_le_mul_left (3 * L * A * D) hW
  calc
    L * (n + A * (1 + 3 * D * W₀)) = n * L + L * A + 3 * L * A * D * W₀ := by ring
    _ ≤ n * L + (3 * (L * A) + 10) + 3 * L * A * D * W :=
      Nat.add_le_add (by omega) hm
    _ = _ := by ring

/-- INTERNAL: Sum the reached history, restart, observation-prefix, and
stopped-site budgets without unfolding the concrete schedule. -/
private theorem observation_cursor_arithmetic (n L B N C j k u v w bits : ℕ)
    (hj : j + 1 ≤ L) (hk : k + 1 ≤ N)
    (hc : u ≤ j * (n + (B + N) * C))
    (hs : v ≤ u + n + B * C) (ho : w ≤ v + k * C)
    (hd : bits ≤ w + C) : bits ≤ L * (n + (B + N) * C) := by
  have hkC := Nat.mul_le_mul_right C hk
  have hjC := Nat.mul_le_mul_right (n + (B + N) * C) hj
  simp only [Nat.add_mul, Nat.one_mul] at hc hkC hjC ⊢
  omega

/-- INTERNAL: Normalize the observation-count record update while the schedule
is generic. Instantiating the unnormalized bound with the concrete schedule
causes excessive kernel reduction when composing cursor budgets.
TEXLINE: main.tex:1350-1390,1392-1421 -/
private theorem observe_prefix_bit_bound {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool)
    (s : AnnealingSchedule) (q : ℚ) (weights : Multipliers n)
    (start : PairedSet n × ℕ) (K k : ℕ)
    (hq : binaryRatLength 1 + n * binaryRatLength q ≤ K)
    (hw : ∀ i, binaryRatLength (weights i) ≤ K)
    (out : ObservationCursor n)
    (h : (observePhase r o₁ o₂ tape {s with observations := k} q weights start).val = some out) :
    out.bitCursor ≤ start.2 + k * (1 + 3 * s.drawTrials * (4 * K + n + 1)) := by
  exact PhaseBitCursorBound.observe_phase_bit_bound r o₁ o₂ tape
    {s with observations := k} q weights start K hq hw out h



end CountingMatroid.Analysis.ObservationRoundDrawSiteCovered

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* maintenance · validated · isolated the kernel stall to composing the observation cursor bound; introduced a generic record-update bridge and retained the complete theorem and every hypothesis. The full standalone proof passed kernel validation in 9.6 seconds before publication.

* this round · blocked on validation · retained the full target proof without a new open obligation; support elaborations passed, but parent import loading did not complete, and no granted build permission was observed.

* this round · verification pending · all eight public support lemmas passed standalone elaboration; both certification waves were mechanically rejected without a diagnostic. Parent checks have encountered transient missing imports or stalled before the first post-import checkpoint; the complete proof text is preserved.

* this round · continued vertically · the live handoff was mechanically rejected without further diagnostic; completed the actual-history cursor induction and retained all owned support files. Parent verification and final publication are pending.

* this round · decomposed · proved tight multiplier, capped-draw, trace-return, restart, and observation budgets; the parent uses the isolated actual-history cursor induction. Scheduled child certification is pending; no prior assumption or statement change was introduced.

* r27 · refined blocker · applied the proved phase-fold size invariant and instantiated weightOfKind_work_size; the resulting (j+1)*runSize^10 bound is too coarse for the fixed quartic tape width, so a tighter multiplier-update bound remains necessary.

* r27 · attempted · unfolded the actual stopped-site history and coarse block budget; PhaseChainWork's per-weight bound requires a quantitative stored-table length invariant and a phase-global restart-attempt count, neither supplied by value-only good multipliers.
-/

end
set_option autoImplicit false

/-!
The quantitative finite-block obligation for the concrete observation draw
stopping maps. The bound must account for all earlier actual phase updates,
restart attempts, and k observations. The additive multiplier, draw, restart, observation, and actual-history
budgets are proved in the support modules. The target proof combines prefix
replay for the lower endpoint with the quartic bound for the full trial interval.
The generic observation-prefix bridge checks record-update projections before
instantiation with the concrete schedule, keeping the composed budget proof
small enough for kernel validation.
-/

namespace CountingMatroid.Analysis.ObservationRoundDrawSiteCovered
end CountingMatroid.Analysis.ObservationRoundDrawSiteCovered
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ObservationRoundDrawSiteCovered

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.PhaseObservationExperiment
open CountingMatroid.Analysis.ObservationRoundDrawSites

/-- INTERNAL: Every stopped observation draw has its cursor after the
external consumed prefix and enough remaining block space for all trials.
TEXLINE: main.tex:1350-1390,1392-1421 -/
theorem solution (n r : ℕ)
    (M₁ M₂ : Matroid (Fin n)) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (hn : 0 < n) (hfull : FullGround M₁ M₂)
    (hr : CommonRank r M₁ M₂) (h₁ : ExactOracle M₁ o₁)
    (h₂ : ExactOracle M₂ o₂) (hpositive : 0 < commonBaseCount M₁ M₂)
    (j : ℕ) (hj : j < (CountingMatroid.Interface.Pseudocode.setup n p).L)
    (pref : List Bool) (hprefix : SuccessfulPhasePrefix n r o₁ o₂ p j pref)
    (k : ℕ) (hk : k < (CountingMatroid.Interface.Pseudocode.setup n p).observations) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    let m := CountingMatroid.Model.Run.blockLength n r p
    let t := m - pref.length
    ∀ site suffix, suffix.length = t → ∀ d,
      observationDrawSite n r o₁ o₂ p j pref k site suffix = some d →
      pref.length ≤ d.1 ∧ d.1 + s.drawTrials * ((d.2 - 1).log2 + 1) ≤ m := by
  /- Validation history: Standalone parent
     checks first reported transient missing ChainStepBitBound/PhaseBitCursorBound
     object files. After publication, checks (including a one-thread bounded
     diagnostic and the generated Lake setup) stalled loading imports. A scratch
     IO checkpoint immediately after the same imports was never reached.
     All three support-source checks passed; no target proof error was emitted.
     Subsequent isolation identified kernel reduction during cursor-budget
     composition; observe_prefix_bit_bound avoids that conversion. -/
  classical
  let s := CountingMatroid.Interface.Pseudocode.setup n p
  let m := CountingMatroid.Model.Run.blockLength n r p
  let K := 4 + n * (4 + s.L * binaryRatLength s.ρ) + 6 +
    s.L * (n * n * (4 * (s.observations + 4)))
  let C := 1 + 3 * s.drawTrials * (4 * K + n + 1)
  have hone : binaryRatLength (1 : ℚ) = 4 := by decide
  let A := 4 + n * (4 + s.L * binaryRatLength s.ρ)
  let U := s.L * (n * n * (4 * (s.observations + 4)))
  have hq : binaryRatLength 1 + n * (binaryRatLength 1 + s.L * binaryRatLength s.ρ) ≤ K := by
    have ha : A ≤ A + 6 + U :=
      (Nat.le_add_right A 6).trans (Nat.le_add_right (A + 6) U)
    simpa only [hone, A, U] using ha
  have hw : 6 + s.L * (n * n * (4 * (s.observations + 4))) ≤ K := by
    change 6 + U ≤ A + 6 + U
    exact (Nat.le_add_right (6 + U) A).trans_eq
      ((Nat.add_comm (6 + U) A).trans (Nat.add_assoc A 6 U).symm)
  dsimp only
  intro site suffix hlen d hsite
  unfold observationDrawSite at hsite
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hsite
  obtain ⟨current, hhistory, start, hrestart, reached, hobserve, hsite⟩ := hsite
  let tape : ℕ → Bool := fun i => ((pref ++ suffix)[i]?).getD false
  have hlower : pref.length ≤ d.1 := by
    obtain ⟨bits, original, hbits, hprevious, horiginal, hgood, hpref, hprefLength⟩ :=
      SuccessfulPrefixAbortBound.successful_prefix_has_good_cursor n r o₁ o₂ p j hj pref hprefix
    have hsame : BoundedRunPhaseHistory.phaseHistory r o₁ o₂ tape s j = some original := by
      by_cases hwithin : original.bitCursor ≤ m
      · apply SuccessfulPhaseReplay.successful_history_replay_of_phase_replay r o₁ o₂ s
          (SinglePhaseIntervalReplay.single_phase_interval_replay r o₁ o₂ s)
          (fun i => (bits[i]?).getD false) j original horiginal tape
        intro i hi
        have hipref : i < pref.length := by
          rw [hpref, List.length_take, hbits, Nat.min_eq_left hwithin]
          exact hi
        dsimp only [tape]
        rw [List.getElem?_append_left hipref, hpref, List.getElem?_take_of_lt hi]
      · have hprefFull : pref = bits := by rw [hpref, List.take_of_length_le (by omega)]
        have hsuffix : suffix = [] := by
          apply List.length_eq_zero_iff.mp
          rw [hlen, hprefFull, hbits, Nat.sub_self]
        simpa only [tape, hprefFull, hsuffix, List.append_nil] using horiginal
    have heq : original = current := Option.some.inj (hsame.symm.trans hhistory)
    have hpre : pref.length ≤ current.bitCursor := by rw [← heq, hprefLength]; exact Nat.min_le_left _ _
    have hs := (RestartPhaseIntervalReplay.restartPhase_success_interval r o₁ o₂ s
      current.tables j current.bitCursor tape start hrestart).1
    have ho := (ObservePhaseIntervalReplay.observePhase_success_interval r o₁ o₂
      {s with observations := k} (s.ρ ^ j) current.currentWeights start tape reached hobserve).1
    split at hsite
    · cases hsite
    · exact hpre.trans (hs.trans (ho.trans
        (chainDrawSite_success_interval r o₁ o₂ s (s.ρ ^ j) current.currentWeights
          reached.state reached.bitCursor site tape d hsite).1))
  refine ⟨hlower, ?_⟩
  have hsize := PhaseHistoryMultiplierLength.phase_history_multiplier_length_le
    r o₁ o₂ tape s j current hhistory
  have hweights : ∀ i, binaryRatLength (current.currentWeights i) ≤ K := by
    intro i
    exact (hsize.1 i).trans ((Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_of_lt hj : j ≤ s.L)) _).trans hw)
  have htables : ∀ phase i, binaryRatLength (current.tables phase i) ≤ K := by
    intro phase i
    exact (hsize.2 phase i).trans ((Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_of_lt hj : j ≤ s.L)) _).trans hw)
  have hqj : binaryRatLength 1 + n * binaryRatLength (s.ρ ^ j) ≤ K := by
    have hp := BoundedRunResourceEnvelope.ratPower_binary_length_le s.ρ j
    rw [CountingMatroid.Analysis.BoundedRunResourceEnvelope.ratPower_value_import_support] at hp
    have hm := Nat.mul_le_mul_right (binaryRatLength s.ρ) (show j ≤ s.L from Nat.le_of_lt hj)
    exact (Nat.add_le_add_left (Nat.mul_le_mul_left n (hp.trans (Nat.add_le_add_left hm _))) _).trans hq
  have hh := PhaseBitCursorBound.phase_history_bit_bound r o₁ o₂ tape s j K
    (Nat.le_of_lt hj) hq hw current hhistory
  have hs := PhaseBitCursorBound.restart_phase_bit_bound r o₁ o₂ tape s current.tables j
    current.bitCursor K (Nat.le_of_lt hj) hq htables start hrestart
  have ho := observe_prefix_bit_bound r o₁ o₂ tape s
    (s.ρ ^ j) current.currentWeights start K k hqj hweights reached hobserve
  split at hsite
  · cases hsite
  · have hd := ChainStepBitBound.chain_draw_site_bit_bound r o₁ o₂ tape s (s.ρ ^ j)
      current.currentWeights reached.state reached.bitCursor K hqj hweights site d hsite
    have hsum : d.1 + s.drawTrials * ((d.2 - 1).log2 + 1) ≤
        s.L * (n + (s.restartCap + s.observations) * C) := by
      exact observation_cursor_arithmetic n s.L s.restartCap s.observations C j k
        current.bitCursor start.2 reached.bitCursor
        (d.1 + s.drawTrials * ((d.2 - 1).log2 + 1))
        (Nat.succ_le_of_lt hj) (Nat.succ_le_of_lt hk) hh hs ho hd
    apply hsum.trans
    have hwidth := quartic_width_covers n s.L s.observations (binaryInputLength n r p)
      (binaryRatLength s.ρ) (setup_rho_length_bound n p hn)
    let W := 1000000 * (s.L + 1) ^ 4 * (n + 1) ^ 4 *
      (s.observations + 1) ^ 4 * (binaryInputLength n r p + 1) ^ 4
    have hcalls : s.drawCalls = 3 * s.L * (s.restartCap + s.observations) := setup_draw_calls_eq n p
    have hblock : m = n * s.L + s.drawCalls * (1 + s.drawTrials * W) + 10 := by
      dsimp only [m, s, W, CountingMatroid.Interface.Pseudocode.setup,
        CountingMatroid.Model.Run.blockLength]
    exact ((draw_budget_arithmetic n s.L (s.restartCap + s.observations) s.drawTrials
      (4 * K + n + 1) W hwidth).trans_eq
      (congrArg (fun calls => n * s.L + calls * (1 + s.drawTrials * W) + 10) hcalls.symm)).trans_eq hblock.symm
