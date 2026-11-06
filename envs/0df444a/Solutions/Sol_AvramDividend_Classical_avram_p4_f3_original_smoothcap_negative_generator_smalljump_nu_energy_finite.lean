-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f3_original_smoothcap_negative_generator_smalljump_nu_energy_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:13:09.265375+00:00
-- url     : https://prove2.me/submissions/a2bad2dc-81c6-4cc8-8886-6a87c989a2ee

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_smoothcap_negative_jump_taylor_quadratic_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original Lévy compensator's small-mark C2 generator remainder has finite energy, uniformly in positive reserves. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a δ K : ℝ) (hδ : 0 < δ) (hδK : δ < K)
    (hKa : K < a) (ha : ENNReal.ofReal a < C) :
    ∃ r : ℝ, 0 < r ∧ r ≤ min δ 1 ∧
      ∀ u ∈ Icc δ K,
        (∫⁻ z in Ioo (-r) (0 : ℝ),
          ENNReal.ofReal
            ‖SpectrallyNegativeLevy.generatorIntegrand w u z‖ ∂X.ν) < ⊤ := by
  obtain ⟨r, B, hr0, hrMax, hB0, hB⟩ :=
    avram_p4_f3_original_smoothcap_negative_jump_taylor_quadratic_bound
      X w C hw_smooth a δ K hδ hδK hKa ha
  refine ⟨r, hr0, hrMax, ?_⟩
  let b : ℝ → ℝ≥0∞ :=
    fun z => ENNReal.ofReal (min (1 : ℝ) (z ^ 2))
  have hb : Measurable b :=
    ENNReal.measurable_ofReal.comp
      (measurable_const.min (measurable_id.pow_const 2))
  have hBoundFin : (∫⁻ z, ENNReal.ofReal B * b z ∂X.ν) < ⊤ := by
    rw [lintegral_const_mul (ENNReal.ofReal B) hb]
    exact ENNReal.mul_lt_top (by simp) X.ν_integrable
  intro u hu
  have hr1 : r ≤ 1 := le_trans hrMax (min_le_right _ _)
  have hPoint (z : ℝ) :
      (Ioo (-r) (0 : ℝ)).indicator
        (fun z => ENNReal.ofReal
          ‖SpectrallyNegativeLevy.generatorIntegrand w u z‖) z
      ≤ ENNReal.ofReal B * b z := by
    by_cases hz : z ∈ Ioo (-r) (0 : ℝ)
    · rw [Set.indicator_of_mem hz]
      have hzLow : -1 < z := by linarith [hz.1, hr1]
      have hzSq : z ^ 2 ≤ (1 : ℝ) := by
        have ht : 0 ≤ (1 + z) * (1 - z) :=
          mul_nonneg (by linarith) (by linarith [hz.2])
        nlinarith
      have hmin : min (1 : ℝ) (z ^ 2) = z ^ 2 :=
        min_eq_right hzSq
      have hReal := hB u hu z hz
      have hEnn := ENNReal.ofReal_le_ofReal hReal
      rw [ENNReal.ofReal_mul hB0] at hEnn
      simpa only [b, hmin] using hEnn
    · rw [Set.indicator_of_notMem hz]
      exact bot_le
  calc
    (∫⁻ z in Ioo (-r) (0 : ℝ),
      ENNReal.ofReal
        ‖SpectrallyNegativeLevy.generatorIntegrand w u z‖ ∂X.ν)
        = ∫⁻ z, (Ioo (-r) (0 : ℝ)).indicator
            (fun t => ENNReal.ofReal
              ‖SpectrallyNegativeLevy.generatorIntegrand w u t‖) z ∂X.ν :=
          (lintegral_indicator measurableSet_Ioo _).symm
    _ ≤ ∫⁻ z, ENNReal.ofReal B * b z ∂X.ν :=
          lintegral_mono hPoint
    _ < ⊤ := hBoundFin
