-- Prove2me | solution 1 for CountingMatroid.Analysis.RestartAttemptBudget.restart_attempt_budget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:28:54.905395+00:00
-- url     : https://prove2.me/submissions/29701164-9ed9-4fa9-9daa-a491d1e59790

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
import Definitions.Def_CountingMatroid_Analysis_ObservePhaseWork
import Definitions.Def_CountingMatroid_Analysis_PhaseChainWork
import Definitions.Def_CountingMatroid_Analysis_PhaseMeanCertificate
import Definitions.Def_CountingMatroid_Analysis_PhaseObservationExperiment
import Definitions.Def_CountingMatroid_Analysis_PhaseResourcePrimitives
import Definitions.Def_CountingMatroid_Analysis_RationalHeight
import Definitions.Def_CountingMatroid_Analysis_RelativeObservationBounds
import Definitions.Def_CountingMatroid_Analysis_RestartAttemptAccounting
import Definitions.Def_CountingMatroid_Analysis_RestartAttemptBudget
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
import Theorems.Thm_CountingMatroid_Analysis_ChainStepBitBound_chain_step_bit_bound
import Theorems.Thm_CountingMatroid_Analysis_PhaseBitCursorBound_phase_history_bit_bound
import Theorems.Thm_CountingMatroid_Analysis_PhaseHistoryMultiplierLength_phase_history_multiplier_length_le

namespace CountingMatroid.Analysis.FiniteObservationMarkov
end CountingMatroid.Analysis.FiniteObservationMarkov
namespace CountingMatroid.Analysis.FiniteTapePrefixBound
end CountingMatroid.Analysis.FiniteTapePrefixBound
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
namespace CountingMatroid.Analysis.PhaseBitCursorBound
end CountingMatroid.Analysis.PhaseBitCursorBound
namespace CountingMatroid.Analysis.PhaseHistoryMultiplierLength
end CountingMatroid.Analysis.PhaseHistoryMultiplierLength
namespace CountingMatroid.Analysis.ChainStepBitBound
end CountingMatroid.Analysis.ChainStepBitBound
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
A uniform per-attempt bit allowance for the restart that follows a reached,
certified history. Every successful chain step at a stored parameter level
advances the cursor by at most C bits, and the whole shared attempt cap,
started after the history's cursor and the fresh transversal, fits in the
finite block. The schedule arithmetic reproduces private helpers of
RestartPhaseBitCoverage, whose public theorem covers only successful restarts.
-/
namespace CountingMatroid.Analysis.RestartAttemptBudget
open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.RestartAttemptAccounting

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



end CountingMatroid.Analysis.RestartAttemptBudget

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · created · per-attempt bit allowance at stored levels and whole-cap block coverage after a reached history, using the existing history cursor and multiplier-length bounds.
-/

end
set_option autoImplicit false

/-!
A uniform per-attempt bit allowance for the restart that follows a reached,
certified history. Every successful chain step at a stored parameter level
advances the cursor by at most C bits, and the whole shared attempt cap,
started after the history's cursor and the fresh transversal, fits in the
finite block. The schedule arithmetic reproduces private helpers of
RestartPhaseBitCoverage, whose public theorem covers only successful restarts.
-/
namespace CountingMatroid.Analysis.RestartAttemptBudget
end CountingMatroid.Analysis.RestartAttemptBudget
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.RestartAttemptBudget
open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.RestartAttemptAccounting

/-- INTERNAL: One allowance C bounds every chain step at a stored level, and the
whole shared attempt cap after the fresh scan fits in the finite block.
TEXLINE: main.tex:1350-1390,1392-1421 -/
theorem solution (n r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (p : InputParams) (hn : 0 < n) (j : ℕ)
    (hj : j < (CountingMatroid.Interface.Pseudocode.setup n p).L)
    (pref : List Bool) (history : RestartPrefixWitness n r o₁ o₂ p j pref) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    ∃ C : ℕ, history.current.bitCursor + n + s.restartCap * C ≤
        CountingMatroid.Model.Run.blockLength n r p ∧
      ∀ a ≤ s.L, ∀ (tape : ℕ → Bool) (state : PairedSet n) (cursor : ℕ)
        (out : PairedSet n × ℕ),
        (chainStep r o₁ o₂ tape s.drawTrials (s.ρ ^ a) (history.current.tables a)
          state cursor).val = some out → out.2 ≤ cursor + C := by
  let s := CountingMatroid.Interface.Pseudocode.setup n p
  let tape := fun i : ℕ => (history.bits[i]?).getD false
  let current := history.current
  have hhistory : BoundedRunPhaseHistory.phaseHistory r o₁ o₂ tape s j = some current :=
    history.reached
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
    omega
  have hsize := PhaseHistoryMultiplierLength.phase_history_multiplier_length_le
    r o₁ o₂ tape s j current hhistory
  have htables : ∀ phase i, binaryRatLength (current.tables phase i) ≤ K := by
    intro phase i
    exact (hsize.2 phase i).trans ((Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_of_lt hj : j ≤ s.L)) _).trans hw)
  refine ⟨C, ?_, ?_⟩
  · have hh := PhaseBitCursorBound.phase_history_bit_bound r o₁ o₂ tape s j K
      (Nat.le_of_lt hj) hq hw current hhistory
    have hsum : current.bitCursor + n + s.restartCap * C ≤
        s.L * (n + (s.restartCap + s.observations) * C) := by
      have hprod := Nat.mul_le_mul_right (n + (s.restartCap + s.observations) * C)
        (Nat.succ_le_of_lt hj)
      change (j+1) * (n + (s.restartCap + s.observations) * C) ≤
        s.L * (n + (s.restartCap + s.observations) * C) at hprod
      change current.bitCursor ≤ j * (n + (s.restartCap + s.observations) * C) at hh
      calc
        current.bitCursor + n + s.restartCap * C ≤
            j * (n + (s.restartCap + s.observations) * C) + n + s.restartCap * C := by omega
        _ ≤ (j+1) * (n + (s.restartCap + s.observations) * C) := by
          nlinarith only [Nat.zero_le (s.observations * C)]
        _ ≤ _ := hprod
    apply hsum.trans
    have hwidth := quartic_width_covers n s.L s.observations (binaryInputLength n r p)
      (binaryRatLength s.ρ) (setup_rho_length_bound n p hn)
    let W := 1000000 * (s.L + 1) ^ 4 * (n + 1) ^ 4 *
      (s.observations + 1) ^ 4 * (binaryInputLength n r p + 1) ^ 4
    have hcalls : s.drawCalls = 3 * s.L * (s.restartCap + s.observations) :=
      setup_draw_calls_eq n p
    have hblock : CountingMatroid.Model.Run.blockLength n r p =
        n * s.L + s.drawCalls * (1 + s.drawTrials * W) + 10 := by
      dsimp only [s, W, CountingMatroid.Interface.Pseudocode.setup,
        CountingMatroid.Model.Run.blockLength]
    exact ((draw_budget_arithmetic n s.L (s.restartCap + s.observations) s.drawTrials
      (4 * K + n + 1) W hwidth).trans_eq
      (congrArg (fun calls => n * s.L + calls * (1 + s.drawTrials * W) + 10)
        hcalls.symm)).trans_eq hblock.symm
  · intro a ha tape' state cursor out hstep
    have hqa : binaryRatLength 1 + n * binaryRatLength (s.ρ ^ a) ≤ K := by
      have hl := BoundedRunResourceEnvelope.ratPower_binary_length_le s.ρ a
      rw [CountingMatroid.Analysis.BoundedRunResourceEnvelope.ratPower_value_import_support] at hl
      have hm := Nat.mul_le_mul_right (binaryRatLength s.ρ) ha
      exact (Nat.add_le_add_left (Nat.mul_le_mul_left n
        (hl.trans (Nat.add_le_add_left hm _))) _).trans hq
    exact ChainStepBitBound.chain_step_bit_bound r o₁ o₂ tape' s.drawTrials (s.ρ ^ a)
      (current.tables a) state cursor K hqa (htables a) out hstep
