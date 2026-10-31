-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_05_gaussian_source_crossing_quadratic_strip
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T07:15:33.268322+00:00
-- url     : https://prove2.me/submissions/271b4f03-fca4-4e64-ae7b-b36c51522e4b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave3_05_gaussian_scale_origin_linear_bound
import Theorems.Thm_AvramDividend_Classical_scaleFunction_zero_origin_gaussian_without_standing
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_two_of_gaussian
import Theorems.Thm_AvramDividend_Classical_origin_crossing_compensated_increment_linear_bound
import Theorems.Thm_AvramDividend_Classical_origin_crossing_strip_norm_integral_bound
import Theorems.Thm_AvramDividend_Classical_generatorIntegrand_negative_jump_reflection
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorIntegrand_continuousAt_away_shift_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The genuine Gaussian Lévy generator has a quadratic integrated crossing strip. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ y : ℝ, -1 < y → y < 0 →
        IntegrableOn
          (fun x : ℝ => |SpectrallyNegativeLevy.generatorIntegrand W x y|)
          (Ioo (0 : ℝ) (-y)) ∧
        (∫ x in Ioo (0 : ℝ) (-y),
          |SpectrallyNegativeLevy.generatorIntegrand W x y|) ≤
          C * y ^ 2 := by
  obtain ⟨K, hK, hWK⟩ :=
    avram_wave3_05_gaussian_scale_origin_linear_bound X hX q hq W hW hσ
  have hzero : W 0 = 0 :=
    scaleFunction_zero_origin_gaussian_without_standing X q hq W hW hσ
  have hWneg : ∀ z : ℝ, z ≤ 0 → W z = 0 := by
    intro z hz
    rcases lt_or_eq_of_le hz with hlt | heq
    · exact hW.1 z hlt
    · simpa [heq] using hzero
  have hC2 : ContDiffOn ℝ 2 W (Ioi (0 : ℝ)) :=
    scaleFunction_contDiff_two_of_gaussian X hX q hq W hW hσ
  have hC2unit : ContDiffOn ℝ 2 W (Ioo (0 : ℝ) 1) :=
    hC2.mono (by intro z hz; exact hz.1)
  refine ⟨2 * K, by positivity, ?_⟩
  intro y hy1 hy
  have hr0 : 0 < -y := by linarith
  have hr1 : -y < 1 := by linarith
  have hpoint : ∀ x ∈ Ioo (0 : ℝ) (-y),
      |SpectrallyNegativeLevy.generatorIntegrand W x y| ≤
        (2 * K) * (-y) := by
    intro x hx
    have hxunit : x ∈ Ioc (0 : ℝ) 1 :=
      ⟨hx.1, by linarith [hx.2]⟩
    have hcross : x + y ≤ 0 := by linarith [hx.2]
    have hlinear :=
      origin_crossing_compensated_increment_linear_bound W x y K
        hx.1 hy hcross hK hWneg (hWK x hxunit).1 (hWK x hxunit).2
    have heq :
        SpectrallyNegativeLevy.generatorIntegrand W x y =
          W (x + y) - W x - deriv W x * y := by
      rw [← generatorIntegrand_negative_jump_reflection W x y hy]
      rw [if_pos hr1]
      ring
    rw [heq]
    exact hlinear
  have hcontinuous : ContinuousOn
      (fun x : ℝ => SpectrallyNegativeLevy.generatorIntegrand W x y)
      (Ioo (0 : ℝ) (-y)) := by
    intro x hx
    have hxunit : x ∈ Ioo (0 : ℝ) 1 :=
      ⟨hx.1, by linarith [hx.2]⟩
    have hshift : x + y ≠ 0 := ne_of_lt (by linarith [hx.2])
    exact (scaleFunction_generatorIntegrand_continuousAt_away_shift_zero
      X q W hW 1 x y hxunit hC2unit hshift).continuousWithinAt
  have hmeas : AEStronglyMeasurable
      (fun x : ℝ => |SpectrallyNegativeLevy.generatorIntegrand W x y|)
      (volume.restrict (Ioo (0 : ℝ) (-y))) :=
    hcontinuous.abs.aestronglyMeasurable measurableSet_Ioo
  have hfinite :
      (volume : Measure ℝ) (Ioo (0 : ℝ) (-y)) < ⊤ := by
    simp
  have hnorm : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) (-y))),
      ‖|SpectrallyNegativeLevy.generatorIntegrand W x y|‖ ≤
        (2 * K) * (-y) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    simpa only [Real.norm_eq_abs, abs_abs] using hpoint x hx
  have hint : IntegrableOn
      (fun x : ℝ => |SpectrallyNegativeLevy.generatorIntegrand W x y|)
      (Ioo (0 : ℝ) (-y)) :=
    IntegrableOn.of_bound hfinite hmeas ((2 * K) * (-y)) hnorm
  exact ⟨hint, origin_crossing_strip_norm_integral_bound
    (fun x : ℝ => SpectrallyNegativeLevy.generatorIntegrand W x y)
    y (2 * K) hy hint hpoint⟩
