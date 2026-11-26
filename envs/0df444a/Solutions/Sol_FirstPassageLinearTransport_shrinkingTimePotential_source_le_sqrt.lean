-- Prove2me | solution 1 for FirstPassageLinearTransport.shrinkingTimePotential_source_le_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:49:28.444072+00:00
-- url     : https://prove2.me/submissions/2bfcdc3f-61c4-4660-a826-f05ae5217cdc

import Definitions.Def_FirstPassageLinearTransport_ShrinkingTimeSupport
import Definitions.Def_FirstPassageLinearTransport_PolylogTerminalSchedule
import Definitions.Def_FirstPassageLinearTransport_TwoRegimeClock
import Definitions.Def_FirstPassageLinearTransport_ShrinkingSchedules
import Theorems.Thm_FirstPassageLinearTransport_shrinkingSwitchRank_lt_add_one
import Theorems.Thm_FirstPassageLinearTransport_PowerDense_D_pos
import Theorems.Thm_FirstPassageLinearTransport_StageSetup_lowerTolerance_M0
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_driftGap_pos
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
attribute [local simp] FirstPassageLinearTransport.StageSetup.lowerTolerance_M0
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
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


section
namespace FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
private theorem log_le_sqrt_mul
    {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ≤ Real.sqrt (x * Real.log x) := by
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlogx : Real.log x ≤ x := (Real.log_le_sub_one_of_pos (lt_of_lt_of_le zero_lt_one hx)).trans (by linarith)
  have hsqrt0 := Real.sqrt_nonneg (x * Real.log x)
  have hsqrtSq := Real.sq_sqrt (mul_nonneg (zero_le_one.trans hx) hlog0)
  have hsq : Real.log x * Real.log x ≤ x * Real.log x :=
    mul_le_mul_of_nonneg_right hlogx hlog0
  nlinarith
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
    (P : ShrinkingBarrierRunData) {C : ℝ} (hC : 0 ≤ C)
    {M : ℕ} (hM : 1 ≤ M)
    (hSwitch : shrinkingSwitchRank C M < M + 1) :
    1 + 2 * shrinkingTimePotential P M (shrinkingSwitchRank C M) (M + 1) /
        driftGap ≤
      shrinkingTimeSupportConstant P C *
        Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) := by
  let x : ℝ := (M : ℝ) + 2
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  have hx1 : 1 ≤ x := by
    dsimp [x]
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
    nlinarith [show 0 ≤ Real.log x from hlog1.trans' zero_le_one]
  have hlogSqrt := log_le_sqrt_mul hx1
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
  have hSbound : (shrinkingSwitchRank C M : ℝ) ≤
      (C + 1) * Real.sqrt (x * Real.log x) := by
    calc
      (shrinkingSwitchRank C M : ℝ) ≤
          C * Real.log x + 1 := hS.le
      _ ≤ C * Real.sqrt (x * Real.log x) +
          Real.sqrt (x * Real.log x) := by gcongr
      _ = (C + 1) * Real.sqrt (x * Real.log x) := by ring
  have hdHi : 0 < 1 - Real.sqrt (P.rHi : ℝ) := by
    apply sub_pos.mpr
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)]
    norm_num
    exact_mod_cast P.pHi.r_lt_one
  have hdLo : 0 < 1 - (P.rLo : ℝ) := sub_pos.mpr P.pLo.r_lt_one
  have hcoefHi : 0 ≤ P.D + P.tau + 3 := by
    nlinarith [P.D_pos, P.pHi.eta_pos]
  have hcoefLo : 0 ≤ 2 * P.etaLo + 3 := by nlinarith [P.pLo.eta_pos]
  have hpot :
      shrinkingTimePotential P M (shrinkingSwitchRank C M) (M + 1) ≤
        ((P.D + P.tau + 3) / (1 - Real.sqrt (P.rHi : ℝ)) +
          (2 * P.etaLo + 3) * (C + 1) / (1 - (P.rLo : ℝ))) *
            Real.sqrt (x * Real.log x) := by
    rw [shrinkingTimePotential, if_pos hSwitch]
    calc
      ((P.D + P.tau + 3) * Real.sqrt (Real.log ((M : ℝ) + 2)) *
            Real.sqrt (((M + 1 : ℕ) : ℝ))) / (1 - Real.sqrt (P.rHi : ℝ)) +
          ((2 * P.etaLo + 3) * (shrinkingSwitchRank C M : ℝ)) /
            (1 - (P.rLo : ℝ)) ≤
        ((P.D + P.tau + 3) * Real.sqrt (x * Real.log x)) /
            (1 - Real.sqrt (P.rHi : ℝ)) +
          ((2 * P.etaLo + 3) * ((C + 1) *
            Real.sqrt (x * Real.log x))) / (1 - (P.rLo : ℝ)) := by
          apply add_le_add
          · apply (div_le_div_iff_of_pos_right hdHi).2
            simpa [x, mul_assoc] using
              (mul_le_mul_of_nonneg_left hsqrtM hcoefHi)
          · apply (div_le_div_iff_of_pos_right hdLo).2
            exact mul_le_mul_of_nonneg_left hSbound hcoefLo
      _ = ((P.D + P.tau + 3) / (1 - Real.sqrt (P.rHi : ℝ)) +
          (2 * P.etaLo + 3) * (C + 1) / (1 - (P.rLo : ℝ))) *
            Real.sqrt (x * Real.log x) := by ring
  unfold shrinkingTimeSupportConstant
  have hscale0 : 0 ≤ Real.sqrt (x * Real.log x) := Real.sqrt_nonneg _
  calc
    1 + 2 * shrinkingTimePotential P M (shrinkingSwitchRank C M) (M + 1) /
        driftGap ≤
      1 + 2 * (((P.D + P.tau + 3) / (1 - Real.sqrt (P.rHi : ℝ)) +
          (2 * P.etaLo + 3) * (C + 1) / (1 - (P.rLo : ℝ))) *
            Real.sqrt (x * Real.log x)) / driftGap := by
      have hmul := mul_le_mul_of_nonneg_left hpot (by norm_num : (0 : ℝ) ≤ 2)
      have hdiv := div_le_div_of_nonneg_right hmul driftGap_pos.le
      linarith
    _ ≤ (2 + 2 / driftGap *
        ((P.D + P.tau + 3) / (1 - Real.sqrt (P.rHi : ℝ)) +
          (2 * P.etaLo + 3) * (C + 1) / (1 - (P.rLo : ℝ)))) *
            Real.sqrt (x * Real.log x) := by
      have hid :
          (2 + 2 / driftGap *
              ((P.D + P.tau + 3) / (1 - Real.sqrt (P.rHi : ℝ)) +
                (2 * P.etaLo + 3) * (C + 1) / (1 - (P.rLo : ℝ)))) *
                Real.sqrt (x * Real.log x) -
            (1 + 2 * (((P.D + P.tau + 3) /
                (1 - Real.sqrt (P.rHi : ℝ)) +
                (2 * P.etaLo + 3) * (C + 1) / (1 - (P.rLo : ℝ))) *
                  Real.sqrt (x * Real.log x)) / driftGap) =
              2 * Real.sqrt (x * Real.log x) - 1 := by ring
      linarith
end FirstPassageLinearTransport
