-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_fin30_original_compact_kernel_product_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T17:50:40.54619+00:00
-- url     : https://prove2.me/submissions/a257b8b8-c6ba-460f-a33a-fb79028d4e80

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin28_original_compact_compensated_kernel_uniform
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin29_finite_product_bounded_kernel_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω α : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace α]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (q u v : ℝ) (hq : 0 < q) (hu : 0 < u) (huv : u < v)
    (hvC : ENNReal.ofReal v < C)
    (hσ : X.σ ≠ 0)
    (hFiniteActivity : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (μ : Measure α) (hμfinite : μ Set.univ < ⊤)
    (Y : α → ℝ) (hY : ∀ a, Y a ∈ Ico u v)
    (G : α × ℝ → ℝ)
    (hG : ∀ p, G p =
      if p.2 < 0 then SpectrallyNegativeLevy.generatorIntegrand w (Y p.1) p.2
      else 0)
    (hGmeas : AEStronglyMeasurable G
      (μ.prod (X.ν.restrict (Iio (0 : ℝ))))) :
    Integrable G (μ.prod (X.ν.restrict (Iio (0 : ℝ)))) := by
  obtain ⟨B, hB0, hB⟩ :=
    avram_mix_fin28_original_compact_compensated_kernel_uniform
      X w C hC q u v hq hu huv hvC hσ hFiniteActivity
      hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad
  have hνfinite : (X.ν.restrict (Iio (0 : ℝ))) Set.univ < ⊤ := by
    simpa using (lt_top_iff_ne_top.mpr hFiniteActivity)
  have hGbound : ∀ p : α × ℝ, |G p| ≤ B := by
    intro p
    rw [hG p]
    by_cases hz : p.2 < 0
    · simp only [if_pos hz]
      exact hB (Y p.1) (hY p.1) p.2 hz
    · simp only [if_neg hz, abs_zero]
      exact hB0
  exact avram_mix_fin29_finite_product_bounded_kernel_integrable
    μ (X.ν.restrict (Iio (0 : ℝ)))
    hμfinite hνfinite G hGmeas B hB0 hGbound
