-- Prove2me | solution 1 for FirstPassageLinearTransport.eventually_timeoutTimePotential_source_le_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:18:17.45284+00:00
-- url     : https://prove2.me/submissions/f980cac1-2f88-437f-b2af-930c0d326143

import Definitions.Def_FirstPassageLinearTransport_TimeoutRun
import Definitions.Def_FirstPassageLinearTransport_ShrinkingSchedules
import Definitions.Def_FirstPassageLinearTransport_TimeoutTimeSupport
import Theorems.Thm_FirstPassageLinearTransport_PowerDense_D_pos
import Theorems.Thm_FirstPassageLinearTransport_StageSetup_lowerTolerance_M0
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_cons
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_scale
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_zero
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
import Theorems.Thm_FirstPassageLinearTransport_card_boolSupport_cons
import Theorems.Thm_FirstPassageLinearTransport_driftGap_pos
import Theorems.Thm_FirstPassageLinearTransport_eventually_shrinkingSwitchRank_lt_source
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_firstBadLandingEnvelope
import Theorems.Thm_FirstPassageLinearTransport_mem_generatedFirstBadSources
import Theorems.Thm_FirstPassageLinearTransport_mem_landingBad
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTaggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTransportedSources
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTransportedSourcesAtTimes
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_mem_shrinkingFeasibleTimes
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
import Theorems.Thm_FirstPassageLinearTransport_shrinkingHighSetup_M0
import Theorems.Thm_FirstPassageLinearTransport_shrinkingSwitchRank_lt_add_one
import Theorems.Thm_FirstPassageLinearTransport_stageClock_zero
import Theorems.Thm_FirstPassageLinearTransport_stageOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_stoppedBallotValue_cons
attribute [local simp] FirstPassageLinearTransport.StageSetup.lowerTolerance_M0
attribute [local simp] FirstPassageLinearTransport.ballotWordValue_cons
attribute [local simp] FirstPassageLinearTransport.ballotWordValue_scale
attribute [local simp] FirstPassageLinearTransport.ballotWordValue_zero
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
attribute [local simp] FirstPassageLinearTransport.bootstrapC_zero
attribute [local simp] FirstPassageLinearTransport.bootstrapD_zero
attribute [local simp] FirstPassageLinearTransport.bootstrapSet_zero
attribute [local simp] FirstPassageLinearTransport.card_boolSupport_cons
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_firstBadLandingEnvelope
attribute [local simp] FirstPassageLinearTransport.mem_generatedFirstBadSources
attribute [local simp] FirstPassageLinearTransport.mem_landingBad
attribute [local simp] FirstPassageLinearTransport.mem_lossFilteredTaggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_lossFilteredTransportedSources
attribute [local simp] FirstPassageLinearTransport.mem_lossFilteredTransportedSourcesAtTimes
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.mem_shrinkingFeasibleTimes
attribute [local simp] FirstPassageLinearTransport.mem_taggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_transportedSources
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.rawOrbit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero
attribute [local simp] FirstPassageLinearTransport.shrinkingHighSetup_M0
attribute [local simp] FirstPassageLinearTransport.stageClock_zero
attribute [local simp] FirstPassageLinearTransport.stageOrbit_zero
attribute [local simp] FirstPassageLinearTransport.stoppedBallotValue_cons


section
namespace FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
private theorem timeout_sqrt_rat_lt_one
    {r : ℚ} (hr1 : r < 1) :
    Real.sqrt (r : ℝ) < 1 := by
  rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)]
  norm_num
  exact_mod_cast hr1
private theorem eventually_timeout_log_sq_le_sqrt_mul :
    ∀ᶠ M : ℕ in atTop,
      (Real.log ((M : ℝ) + 2)) ^ 2 ≤
        Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) := by
  have hsmallReal :=
    (Real.isLittleO_pow_log_id_atTop (n := 3)).bound
      (by norm_num : (0 : ℝ) < 1)
  have hxT : Tendsto (fun M : ℕ => (M : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop (2 : ℝ)
      tendsto_natCast_atTop_atTop
  have hsmall := hxT.eventually hsmallReal
  filter_upwards [hsmall, eventually_ge_atTop (1 : ℕ)] with M hsmall hM
  let x : ℝ := (M : ℝ) + 2
  have hx1 : 1 ≤ x := by
    dsimp [x]
    have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
    linarith
  have hx0 : 0 ≤ x := zero_le_one.trans hx1
  have hlog1 : 1 ≤ Real.log x := by
    apply (Real.le_log_iff_exp_le (by positivity)).2
    have he : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
    dsimp [x]
    have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
    linarith
  have hlog0 : 0 ≤ Real.log x := zero_le_one.trans hlog1
  have hlogCube0 : 0 ≤ (Real.log x) ^ 3 := by positivity
  have hsmall' : (Real.log x) ^ 3 ≤ x := by
    simpa [x, id_eq, Real.norm_eq_abs, abs_of_nonneg hlogCube0,
      abs_of_nonneg hlog0, abs_of_nonneg hx0] using hsmall
  have hfourth : (Real.log x) ^ 4 ≤ x * Real.log x := by
    nlinarith [mul_le_mul_of_nonneg_right hsmall' hlog0]
  have hroot0 := Real.sqrt_nonneg (x * Real.log x)
  have hrootSq := Real.sq_sqrt (mul_nonneg hx0 hlog0)
  dsimp [x] at *
  nlinarith [sq_nonneg ((Real.log ((M : ℝ) + 2)) ^ 2 -
    Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)))]
end
end FirstPassageLinearTransport
end

set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    (P : TimeoutHighRunData) {C : ℝ} (hC : 0 ≤ C) :
    ∀ᶠ M : ℕ in atTop,
      1 + 2 * timeoutTimePotential P M (shrinkingSwitchRank C M) (M + 1) /
          driftGap ≤
        timeoutTimeSupportConstant P C *
          Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) := by
  filter_upwards [eventually_timeout_log_sq_le_sqrt_mul,
      eventually_shrinkingSwitchRank_lt_source hC,
      eventually_ge_atTop (1 : ℕ)] with M hlogSq hSwitch hM
  let x : ℝ := (M : ℝ) + 2
  have hx1 : 1 ≤ x := by
    dsimp [x]
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    linarith
  have hlog1 : 1 ≤ Real.log x := by
    apply (Real.le_log_iff_exp_le (by positivity)).2
    have he : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
    have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
    dsimp [x]
    linarith
  have hsqrt1 : 1 ≤ Real.sqrt (x * Real.log x) := by
    rw [← Real.sqrt_one]
    apply Real.sqrt_le_sqrt
    nlinarith [show 0 ≤ Real.log x from zero_le_one.trans hlog1]
  have hsqrtM :
      Real.sqrt (Real.log x) * Real.sqrt ((M + 1 : ℕ) : ℝ) ≤
        Real.sqrt (x * Real.log x) := by
    rw [← Real.sqrt_mul (Real.log_nonneg hx1)]
    apply Real.sqrt_le_sqrt
    have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
    dsimp [x]
    push_cast
    nlinarith
  have hS := shrinkingSwitchRank_lt_add_one hC M
  have hSle : (shrinkingSwitchRank C M : ℝ) ≤
      (C + 5) * Real.log x := by
    have hC5 : 0 ≤ C + 5 := by linarith
    have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
    apply le_of_lt
    calc
      (shrinkingSwitchRank C M : ℝ) < C * Real.log x + 1 := by
        simpa [x] using hS
      _ ≤ (C + 5) * Real.log x := by nlinarith
  have hlow :
      (shrinkingSwitchRank C M : ℝ) ^ 2 ≤
        (C + 5) ^ 2 * Real.sqrt (x * Real.log x) := by
    have hC5 : 0 ≤ C + 5 := by linarith
    have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
    have hS0 : 0 ≤ (shrinkingSwitchRank C M : ℝ) := Nat.cast_nonneg _
    have hsquare :
        (shrinkingSwitchRank C M : ℝ) ^ 2 ≤
          ((C + 5) * Real.log x) ^ 2 := by nlinarith
    calc
      (shrinkingSwitchRank C M : ℝ) ^ 2 ≤
          ((C + 5) * Real.log x) ^ 2 := hsquare
      _ = (C + 5) ^ 2 * (Real.log x) ^ 2 := by ring
      _ ≤ (C + 5) ^ 2 * Real.sqrt (x * Real.log x) := by
        exact mul_le_mul_of_nonneg_left (by simpa [x] using hlogSq) (sq_nonneg _)
  have hdHi : 0 < 1 - Real.sqrt (P.rHi : ℝ) := sub_pos.mpr
    (timeout_sqrt_rat_lt_one
      (by exact_mod_cast P.pHi.r_lt_one : P.rHi < 1))
  have hcoefHi : 0 ≤ P.D + P.tau + 3 := by
    nlinarith [P.D_pos, P.pHi.eta_pos]
  have hpot :
      timeoutTimePotential P M (shrinkingSwitchRank C M) (M + 1) ≤
        ((P.D + P.tau + 3) / (1 - Real.sqrt (P.rHi : ℝ)) +
          (C + 5) ^ 2) * Real.sqrt (x * Real.log x) := by
    rw [timeoutTimePotential,
      if_pos (by omega : shrinkingSwitchRank C M < M + 1)]
    calc
      ((P.D + P.tau + 3) * Real.sqrt (Real.log ((M : ℝ) + 2)) *
            Real.sqrt (((M + 1 : ℕ) : ℝ))) /
              (1 - Real.sqrt (P.rHi : ℝ)) +
          (shrinkingSwitchRank C M : ℝ) ^ 2 ≤
        ((P.D + P.tau + 3) * Real.sqrt (x * Real.log x)) /
              (1 - Real.sqrt (P.rHi : ℝ)) +
          (C + 5) ^ 2 * Real.sqrt (x * Real.log x) := by
        apply add_le_add
        · apply (div_le_div_iff_of_pos_right hdHi).2
          simpa [x, mul_assoc] using
            (mul_le_mul_of_nonneg_left hsqrtM hcoefHi)
        · exact hlow
      _ = ((P.D + P.tau + 3) / (1 - Real.sqrt (P.rHi : ℝ)) +
          (C + 5) ^ 2) * Real.sqrt (x * Real.log x) := by ring
  unfold timeoutTimeSupportConstant
  calc
    1 + 2 * timeoutTimePotential P M (shrinkingSwitchRank C M) (M + 1) /
        driftGap ≤
      1 + 2 * (((P.D + P.tau + 3) /
          (1 - Real.sqrt (P.rHi : ℝ)) + (C + 5) ^ 2) *
            Real.sqrt (x * Real.log x)) / driftGap := by
      have hmul := mul_le_mul_of_nonneg_left hpot (by norm_num : (0 : ℝ) ≤ 2)
      have hdiv := div_le_div_of_nonneg_right hmul driftGap_pos.le
      linarith
    _ ≤ (2 + 2 / driftGap *
        ((P.D + P.tau + 3) / (1 - Real.sqrt (P.rHi : ℝ)) +
          (C + 5) ^ 2)) * Real.sqrt (x * Real.log x) := by
      let B := (P.D + P.tau + 3) / (1 - Real.sqrt (P.rHi : ℝ)) +
        (C + 5) ^ 2
      have hid :
          (2 + 2 / driftGap * B) * Real.sqrt (x * Real.log x) -
            (1 + 2 * (B * Real.sqrt (x * Real.log x)) / driftGap) =
              2 * Real.sqrt (x * Real.log x) - 1 := by ring
      dsimp only [B] at hid
      linarith
end FirstPassageLinearTransport
