-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_01_original_record_log_rate_continuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T21:42:52.118333+00:00
-- url     : https://prove2.me/submissions/e9b41869-62df-41d8-96cd-41a6ca132ae8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_reflected_record_discount_strict_pos
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_reflected_record_factor_continuous_depth_no_grids

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal ENNReal

/-- The genuine source record-discount factor at unit height has a finite,
continuous real negative logarithm on all positive reflected depths. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hnbv : ¬ X.BoundedVariation)
    (hjump : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν) = ⊤) :
    ContinuousOn (fun a : ℝ =>
      -Real.log ((∫⁻ ω,
        if twoSidedExitUpTime X 1 ω < barrierRuinTime X a ω then
          ENNReal.ofReal
            (Real.exp (-(q * (twoSidedExitUpTime X 1 ω).toReal)))
        else 0 ∂P).toReal)) (Ioi 0) := by
  let F : ℝ → ℝ≥0∞ := fun a =>
    ∫⁻ ω, if twoSidedExitUpTime X 1 ω < barrierRuinTime X a ω then
      ENNReal.ofReal
        (Real.exp (-(q * (twoSidedExitUpTime X 1 ω).toReal)))
    else 0 ∂P
  have hFcont : ContinuousOn F (Ioi 0) := by
    exact avram_wave3_01_reflected_record_factor_continuous_depth_no_grids
      X 1 q (by norm_num) hq hjump
  have hFpos (a : ℝ) (ha : 0 < a) : 0 < F a := by
    exact avram_wave3_01_reflected_record_discount_strict_pos
      X q hq W hW hnbv a ha 1 (by norm_num)
  letI : IsProbabilityMeasure P := X.isProbability
  have hFle (a : ℝ) : F a ≤ 1 := by
    have hpt (ω : Ω) :
        (if twoSidedExitUpTime X 1 ω < barrierRuinTime X a ω then
          ENNReal.ofReal
            (Real.exp (-(q * (twoSidedExitUpTime X 1 ω).toReal)))
        else 0) ≤ (1 : ℝ≥0∞) := by
      split_ifs
      · have ht : 0 ≤ (twoSidedExitUpTime X 1 ω).toReal :=
          ENNReal.toReal_nonneg
        have hqt : 0 ≤ q * (twoSidedExitUpTime X 1 ω).toReal :=
          mul_nonneg hq.le ht
        have he : Real.exp (-(q * (twoSidedExitUpTime X 1 ω).toReal)) ≤ 1 := by
          simpa only [Real.exp_zero] using
            (Real.exp_le_exp.mpr (neg_nonpos.mpr hqt))
        simpa only [ENNReal.ofReal_one] using (ENNReal.ofReal_le_ofReal he)
      · exact zero_le_one
    calc
      F a ≤ ∫⁻ _ : Ω, (1 : ℝ≥0∞) ∂P := lintegral_mono hpt
      _ = 1 := by simp
  have hFtop (a : ℝ) : F a ≠ ⊤ := by
    exact (lt_top_iff_ne_top).mp (lt_of_le_of_lt (hFle a) (by simp))
  intro a ha
  have hRcont : ContinuousAt (fun z : ℝ => (F z).toReal) a :=
    (ENNReal.continuousAt_toReal (hFtop a)).comp
      (hFcont.continuousAt (isOpen_Ioi.mem_nhds ha))
  have hRpos : 0 < (F a).toReal := by
    exact ENNReal.toReal_pos (ne_of_gt (hFpos a ha)) (hFtop a)
  have hLog : ContinuousAt (fun z : ℝ => -Real.log ((F z).toReal)) a :=
    (hRcont.log (ne_of_gt hRpos)).neg
  exact hLog.continuousWithinAt
