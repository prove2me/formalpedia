-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_fin26_original_source_compact_absolute_gradient_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T14:30:24.83035+00:00
-- url     : https://prove2.me/submissions/e74a84ac-7762-4e57-9b2d-ced3d82951bc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin26_original_source_compact_derivative_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
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
      ENNReal.ofReal y < C → 1 ≤ deriv w y) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y ∈ Ico u v, |deriv w y| ≤ K := by
  obtain ⟨B, hB⟩ :=
    avram_mix_fin26_original_source_compact_derivative_bound
      X w C hC q u v hq hu huv hvC hσ hFiniteActivity
      hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad
  have huI : u ∈ Ico u v := ⟨le_refl u, huv⟩
  have huCap : ENNReal.ofReal u < C :=
    (ENNReal.ofReal_le_ofReal (le_of_lt huv)).trans_lt hvC
  have huGrad : 1 ≤ deriv w u := hw_grad u hu huCap
  have hK : 0 ≤ B := by linarith [hB u huI]
  refine ⟨B, hK, ?_⟩
  intro y hy
  have hypos : 0 < y := lt_of_lt_of_le hu hy.1
  have hyCap : ENNReal.ofReal y < C :=
    (ENNReal.ofReal_le_ofReal (le_of_lt hy.2)).trans_lt hvC
  have hyGrad : 1 ≤ deriv w y := hw_grad y hypos hyCap
  rw [abs_of_nonneg (by linarith : 0 ≤ deriv w y)]
  exact hB y hy
