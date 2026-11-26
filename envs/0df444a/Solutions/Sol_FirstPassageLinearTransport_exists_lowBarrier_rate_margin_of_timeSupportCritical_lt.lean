-- Prove2me | solution 1 for FirstPassageLinearTransport.exists_lowBarrier_rate_margin_of_timeSupportCritical_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:01:22.6841+00:00
-- url     : https://prove2.me/submissions/5d47c8dc-01ab-4adf-b7f3-8eae807c275c

import Definitions.Def_FirstPassageLinearTransport_ShrinkingHighDensity
import Definitions.Def_FirstPassageLinearTransport_FixedPolylogParameters
import Definitions.Def_FirstPassageLinearTransport_ShrinkingParameters
import Theorems.Thm_FirstPassageLinearTransport_timeSupportCriticalExponent_gt_half
import Theorems.Thm_FirstPassageLinearTransport_exists_lowBarrier_of_timeSupportCritical_lt
import Theorems.Thm_FirstPassageLinearTransport_StageSetup_lowerTolerance_M0
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_firstBadLandingEnvelope
import Theorems.Thm_FirstPassageLinearTransport_mem_generatedFirstBadSources
import Theorems.Thm_FirstPassageLinearTransport_mem_landingBad
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTaggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTransportedSources
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTransportedSourcesAtTimes
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_mem_shrinkingFeasibleTimes
import Theorems.Thm_FirstPassageLinearTransport_mem_shrinkingFirstBadSourcesAtRank
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
import Theorems.Thm_FirstPassageLinearTransport_shrinkingHighSetup_M0
import Theorems.Thm_FirstPassageLinearTransport_stageClock_zero
import Theorems.Thm_FirstPassageLinearTransport_stageOrbit_zero
attribute [local simp] FirstPassageLinearTransport.StageSetup.lowerTolerance_M0
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
attribute [local simp] FirstPassageLinearTransport.bootstrapC_zero
attribute [local simp] FirstPassageLinearTransport.bootstrapD_zero
attribute [local simp] FirstPassageLinearTransport.bootstrapSet_zero
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_firstBadLandingEnvelope
attribute [local simp] FirstPassageLinearTransport.mem_generatedFirstBadSources
attribute [local simp] FirstPassageLinearTransport.mem_landingBad
attribute [local simp] FirstPassageLinearTransport.mem_lossFilteredTaggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_lossFilteredTransportedSources
attribute [local simp] FirstPassageLinearTransport.mem_lossFilteredTransportedSourcesAtTimes
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.mem_shrinkingFeasibleTimes
attribute [local simp] FirstPassageLinearTransport.mem_shrinkingFirstBadSourcesAtRank
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



set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {A : ℝ} (hA : timeSupportCriticalExponent < A) :
    ∃ lambda t b kappa : ℝ,
      0 ≤ lambda ∧ lambda < 1 ∧
      0 < t ∧ t < driftGap ∧ t < a0 ∧
      0 < b ∧ b < adjustableEntropyRate lambda t ∧
      b < Real.log 2 ∧
      0 < kappa ∧ kappa < A * b / Real.log 2 - 1 / 2 := by
  obtain ⟨lambda, t, hlambda0, hlambda1, ht0, htGap, htA, hrate⟩ :=
    exists_lowBarrier_of_timeSupportCritical_lt hA
  have hAhalf : (1 / 2 : ℝ) < A :=
    timeSupportCriticalExponent_gt_half.trans hA
  have hA0 : 0 < A := by linarith
  let threshold := Real.log 2 / (2 * A)
  let upper := min (adjustableEntropyRate lambda t) (Real.log 2)
  have hthreshold0 : 0 < threshold := by
    dsimp [threshold]
    exact div_pos (Real.log_pos (by norm_num)) (mul_pos (by norm_num) hA0)
  have hthresholdUpper : threshold < upper := by
    rw [lt_min_iff]
    refine ⟨by simpa [threshold] using hrate, ?_⟩
    dsimp [threshold]
    have htwoA : 1 < 2 * A := by linarith
    exact div_lt_self (Real.log_pos (by norm_num)) htwoA
  let b := (threshold + upper) / 2
  have hbLower : threshold < b := by dsimp [b]; linarith
  have hbUpper : b < upper := by dsimp [b]; linarith
  have hb0 : 0 < b := hthreshold0.trans hbLower
  have hbRate : b < adjustableEntropyRate lambda t :=
    hbUpper.trans_le (min_le_left _ _)
  have hbLog : b < Real.log 2 := hbUpper.trans_le (min_le_right _ _)
  have hmargin : 0 < A * b / Real.log 2 - 1 / 2 := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hAb : Real.log 2 / 2 < A * b := by
      have hmul := mul_lt_mul_of_pos_left hbLower hA0
      dsimp [threshold] at hmul
      have htwoA : (2 * A : ℝ) ≠ 0 := ne_of_gt (mul_pos (by norm_num) hA0)
      have hid : A * (Real.log 2 / (2 * A)) = Real.log 2 / 2 := by
        field_simp [htwoA]
      rw [hid] at hmul
      exact hmul
    rw [sub_pos]
    apply (lt_div_iff₀ hlog2).2
    nlinarith
  let kappa := (A * b / Real.log 2 - 1 / 2) / 2
  have hkappa0 : 0 < kappa := by dsimp [kappa]; linarith
  have hkappa : kappa < A * b / Real.log 2 - 1 / 2 := by
    dsimp [kappa]
    linarith
  exact ⟨lambda, t, b, kappa,
    hlambda0, hlambda1, ht0, htGap, htA, hb0, hbRate, hbLog,
    hkappa0, hkappa⟩
end FirstPassageLinearTransport
