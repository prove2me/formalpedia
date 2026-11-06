-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f3_original_smoothcap_negative_jump_taylor_quadratic_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:05:08.464265+00:00
-- url     : https://prove2.me/submissions/995698b2-ab57-4fd0-b770-6e661008ec69

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p3_generator_integrand_uniform_near_C2_quadratic_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The canonical source capped C2 domain controls the true original compensated generator small-mark Taylor remainder. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a δ K : ℝ) (hδ : 0 < δ) (hδK : δ < K)
    (hKa : K < a) (ha : ENNReal.ofReal a < C) :
    ∃ r B : ℝ, 0 < r ∧ r ≤ min δ 1 ∧ 0 ≤ B ∧
      ∀ u ∈ Icc δ K, ∀ z ∈ Ioo (-r) 0,
        ‖SpectrallyNegativeLevy.generatorIntegrand w u z‖
          ≤ B * z ^ 2 := by
  have hC2 : ContDiffOn ℝ 2 w (Ioo 0 a) := by
    apply hw_smooth.mono
    intro y hy
    exact ⟨hy.1, lt_of_le_of_lt
      (ENNReal.ofReal_le_ofReal (le_of_lt hy.2)) ha⟩
  exact avram_wave4_p3_generator_integrand_uniform_near_C2_quadratic_bound
    X w a δ K hδ hδK hKa hC2
