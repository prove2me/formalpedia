-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_fin28_original_compact_compensated_kernel_uniform
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T15:16:59.480831+00:00
-- url     : https://prove2.me/submissions/20003d32-4fa8-45f9-9985-4b19060b31a8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin26_original_source_compact_absolute_gradient_bound
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin26_original_reward_upper_by_interior_cap
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin26_original_reward_nonnegative_below_interior
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin28_original_compensated_kernel_absolute_bound
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
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ y ∈ Ico u v, ∀ z : ℝ, z < 0 →
        |SpectrallyNegativeLevy.generatorIntegrand w y z| ≤ B := by
  obtain ⟨K, hK0, hK⟩ :=
    avram_mix_fin26_original_source_compact_absolute_gradient_bound
      X w C hC q u v hq hu huv hvC hσ hFiniteActivity
      hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad
  have hvpos : 0 ≤ w v :=
    avram_mix_fin26_original_reward_nonnegative_below_interior
      C hC w hw0 hw_cont hw_neg hw_smooth hw_grad
      v (hu.trans huv) hvC v (le_refl v)
  have hwupper :=
    avram_mix_fin26_original_reward_upper_by_interior_cap
      C hC w hw_cont hw_smooth hw_grad u v hu huv hvC
  refine ⟨w v + K, by linarith, ?_⟩
  intro y hy z hz
  have hypos : 0 < y := lt_of_lt_of_le hu hy.1
  have hyC : ENNReal.ofReal y < C :=
    (ENNReal.ofReal_le_ofReal (le_of_lt hy.2)).trans_lt hvC
  have hkernel :=
    avram_mix_fin28_original_compensated_kernel_absolute_bound
      C hC w hw0 hw_cont hw_neg hw_smooth hw_grad
      y z hypos hyC hz
  have hwy : w y ≤ w v := hwupper y hy
  have hderiv := hK y hy
  linarith
