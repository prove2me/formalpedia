-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_05_gaussian_scale_origin_linear_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T01:33:36.002982+00:00
-- url     : https://prove2.me/submissions/5872fad4-25cd-4570-80fc-17df53076773

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave3_05_gaussian_deriv_bounded_near_zero
import Theorems.Thm_AvramDividend_Classical_scaleFunction_zero_origin_gaussian_without_standing
import Theorems.Thm_AvramDividend_Classical_scaleFunction_global_continuous_of_zero_origin
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_two_of_gaussian

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The original Gaussian scale grows at most linearly across the positive origin. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Ioc (0 : ℝ) 1,
      |W x| ≤ C * x ∧ |deriv W x| ≤ C := by
  obtain ⟨C, hC0, hD⟩ :=
    avram_wave3_05_gaussian_deriv_bounded_near_zero
      X hX q hq W hW hσ
  have hzero : W 0 = 0 :=
    scaleFunction_zero_origin_gaussian_without_standing X q hq W hW hσ
  have hcont : Continuous W :=
    scaleFunction_global_continuous_of_zero_origin X q W hW hzero
  have hC2 : ContDiffOn ℝ 2 W (Ioi (0 : ℝ)) :=
    scaleFunction_contDiff_two_of_gaussian X hX q hq W hW hσ
  have hdiff : DifferentiableOn ℝ W (Ioi (0 : ℝ)) :=
    hC2.differentiableOn (by norm_num)
  refine ⟨C, hC0, ?_⟩
  intro x hx
  have hdiffInterval : DifferentiableOn ℝ W (Ioo (0 : ℝ) x) :=
    hdiff.mono (by intro t ht; exact ht.1)
  obtain ⟨c, hc, hSlope⟩ :=
    exists_deriv_eq_slope W hx.1 hcont.continuousOn hdiffInterval
  have hcUnit : c ∈ Ioc (0 : ℝ) 1 :=
    ⟨hc.1, le_trans hc.2.le hx.2⟩
  have hcBound : |deriv W c| ≤ C := hD c hcUnit
  have hSlope' : deriv W c = W x / x := by
    simpa only [hzero, sub_zero] using hSlope
  rw [hSlope'] at hcBound
  have hAbs : |W x / x| = |W x| / x := by
    rw [abs_div, abs_of_pos hx.1]
  rw [hAbs] at hcBound
  exact ⟨(div_le_iff₀ hx.1).mp hcBound, hD x hx⟩
