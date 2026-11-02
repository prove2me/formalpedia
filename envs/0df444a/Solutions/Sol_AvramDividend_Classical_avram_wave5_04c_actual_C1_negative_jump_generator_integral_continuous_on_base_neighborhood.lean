-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04c_actual_C1_negative_jump_generator_integral_continuous_on_base_neighborhood
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T14:17:57.180005+00:00
-- url     : https://prove2.me/submissions/ee0e14dc-67e9-4362-a005-3c7bde286c65

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_boundedVariation_full_negative_jump_increment_integrable
import Theorems.Thm_AvramDividend_Classical_chat07_bv_negative_jump_scalar_majorant_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_global_lipschitz_jump_increment_two_moduli
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set Filter
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (hwC1 : ContDiff ℝ 1 w)
    (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ u v : ℝ, |w u - w v| ≤ L * |u - v|)
    (x : ℝ) (hgen : X.GeneratorIntegrable w x) :
    ContinuousOn (fun z : ℝ =>
      ∫ y : ℝ, (w (z + y) - w z) ∂(X.ν.restrict (Iio 0)))
      (Icc (x - 1) (x + 1)) := by
  let μ : Measure ℝ := X.ν.restrict (Iio 0)
  let K : ℝ → ℝ → ℝ := fun z y => w (z + y) - w z
  let C : ℝ := 2 * L
  have hKx : Integrable (K x) μ := by
    change IntegrableOn (K x) (Iio 0) X.ν
    simpa only [K] using boundedVariation_full_negative_jump_increment_integrable
      X hBV w x hgen
  have hmajor : Integrable (fun y : ℝ => C * min 1 |y|) μ := by
    change IntegrableOn (fun y : ℝ => C * min 1 |y|) (Iio 0) X.ν
    exact chat07_bv_negative_jump_scalar_majorant_integrable X hBV C
  have hdom : Integrable (fun y : ℝ => ‖K x y‖ + C * min 1 |y|) μ :=
    hKx.norm.add hmajor
  have hmeas (z : ℝ) : Measurable (K z) := by
    exact ((hwC1.continuous.measurable.comp
      (measurable_const.add measurable_id)).sub measurable_const)
  have hcontK (y : ℝ) : Continuous (fun z : ℝ => K z y) := by
    exact ((hwC1.continuous.comp
      (continuous_id.add continuous_const)).sub hwC1.continuous)
  have hnorm (z : ℝ) (hz : z ∈ Icc (x - 1) (x + 1)) :
      ∀ᵐ y ∂μ, ‖K z y‖ ≤ ‖K x y‖ + C * min 1 |y| := by
    have hdist : |z - x| ≤ 1 := abs_le.mpr ⟨by linarith [hz.1], by linarith [hz.2]⟩
    filter_upwards [] with y
    have ha := avram_wave5_04c_global_lipschitz_jump_increment_two_moduli
      w L hL hLip x z y
    have hb : min |z - x| |y| ≤ min 1 |y| := min_le_min_right _ hdist
    have hmul : 0 ≤ 2 * L := by positivity
    have hc : ‖K z y - K x y‖ ≤ C * min 1 |y| := by
      calc
        ‖K z y - K x y‖ =
            |(w (z + y) - w z) - (w (x + y) - w x)| := by
          simp only [K, Real.norm_eq_abs]
        _ ≤ 2 * L * min |z - x| |y| := ha
        _ ≤ 2 * L * min 1 |y| := mul_le_mul_of_nonneg_left hb hmul
        _ = C * min 1 |y| := rfl
    calc
      ‖K z y‖ = ‖(K z y - K x y) + K x y‖ := by congr 1; ring
      _ ≤ ‖K z y - K x y‖ + ‖K x y‖ := norm_add_le _ _
      _ ≤ ‖K x y‖ + C * min 1 |y| := by linarith
  have hcont :
      Continuous (fun z : (Icc (x - 1) (x + 1) : Set ℝ) =>
        ∫ y : ℝ, K (z : ℝ) y ∂μ) := by
    apply (continuous_iff_seqContinuous).2
    intro v z hv
    have hv' : Tendsto (fun n => (v n : ℝ)) atTop (nhds (z : ℝ)) :=
      (continuous_subtype_val.tendsto z).comp hv
    have hpoint : ∀ᵐ y ∂μ,
        Tendsto (fun n => K (v n : ℝ) y) atTop (nhds (K (z : ℝ) y)) := by
      filter_upwards [] with y
      exact ((hcontK y).tendsto (z : ℝ)).comp hv'
    exact MeasureTheory.tendsto_integral_of_dominated_convergence
      (bound := fun y : ℝ => ‖K x y‖ + C * min 1 |y|)
      (fun n => (hmeas (v n : ℝ)).aestronglyMeasurable)
      hdom (fun n => hnorm (v n : ℝ) (v n).property) hpoint
  change ContinuousOn (fun z : ℝ => ∫ y : ℝ, K z y ∂μ) (Icc (x - 1) (x + 1))
  exact continuousOn_iff_continuous_restrict.mpr hcont
