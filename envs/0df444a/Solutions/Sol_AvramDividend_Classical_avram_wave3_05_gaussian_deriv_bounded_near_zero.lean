-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_05_gaussian_deriv_bounded_near_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T01:26:51.301728+00:00
-- url     : https://prove2.me/submissions/510110c0-f104-4b95-8e22-1df7b0e73645

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_zero_origin_gaussian_without_standing
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_two_of_gaussian
import Theorems.Thm_AvramDividend_Classical_gaussian_scale_derivative_right_continuous_extension

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The true Gaussian right-origin derivative controls every strictly positive reserve up to one. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ Ioc (0 : ℝ) 1, |deriv W x| ≤ C := by
  have hzero : W 0 = 0 :=
    scaleFunction_zero_origin_gaussian_without_standing
      X q hq W hW hσ
  have hC2 : ContDiffOn ℝ 2 W (Ioi (0 : ℝ)) :=
    scaleFunction_contDiff_two_of_gaussian X hX q hq W hW hσ
  have hdiff : DifferentiableOn ℝ W (Ioi (0 : ℝ)) :=
    hC2.differentiableOn (by norm_num)
  have hHasDeriv : ∀ x ∈ Ioi (0 : ℝ),
      HasDerivAt W (deriv W x) x := by
    intro x hx
    exact (hdiff.differentiableAt (isOpen_Ioi.mem_nhds hx)).hasDerivAt
  let D : ℝ → ℝ :=
    fun x => if x = 0 then 2 / X.σ ^ 2 else deriv W x
  have hDcont : ContinuousOn D (Ici (0 : ℝ)) := by
    simpa only [D] using
      (gaussian_scale_derivative_right_continuous_extension
        X q hq W hW hσ hzero hHasDeriv)
  have hDCap : ContinuousOn D (Icc (0 : ℝ) 1) :=
    hDcont.mono (by intro x hx; exact hx.1)
  have hAbsCap : ContinuousOn (fun x => |D x|) (Icc (0 : ℝ) 1) :=
    continuous_abs.comp_continuousOn' hDCap
  have hBound : BddAbove
      ((fun x : ℝ => |D x|) '' Icc (0 : ℝ) 1) :=
    isCompact_Icc.bddAbove_image hAbsCap
  obtain ⟨C, hC⟩ := hBound
  refine ⟨max C 0, le_max_right C 0, ?_⟩
  intro x hx
  have hxIcc : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2⟩
  have hxBound : |D x| ≤ C := hC (mem_image_of_mem _ hxIcc)
  have hxne : x ≠ 0 := ne_of_gt hx.1
  change |(if x = 0 then 2 / X.σ ^ 2 else deriv W x)| ≤ C at hxBound
  rw [if_neg hxne] at hxBound
  exact hxBound.trans (le_max_left C 0)
