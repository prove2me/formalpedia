-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_fin26_original_source_compact_derivative_uniform
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T14:06:57.333804+00:00
-- url     : https://prove2.me/submissions/378c5f49-09ae-4874-a778-674290e8e3b1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin26_original_finite_cap_derivative_uniform
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin26_original_reward_nonnegative_below_interior
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin26_original_reward_upper_by_interior_cap
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
    (q u v β ε : ℝ) (hq : 0 < q) (hu : 0 < u) (huv : u < v)
    (hvC : ENNReal.ofReal v < C)
    (hβ : 0 ≤ β) (hε : 0 ≤ ε)
    (hA : 0 < X.σ ^ 2 / 2)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hBeta : -X.c ≤ (X.σ ^ 2 / 2) * β)
    (hEps : (q + (X.ν (Iio (0 : ℝ))).toReal) * w v ≤
      (X.σ ^ 2 / 2) * ε) :
    ∃ B : ℝ, ∀ y ∈ Ico u v, deriv w y ≤ B := by
  have hSubset : Ioo (0 : ℝ) v ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := by
    intro y hy
    exact ⟨hy.1,
      (ENNReal.ofReal_le_ofReal (le_of_lt hy.2)).trans_lt hvC⟩
  have hSmooth : ContDiffOn ℝ 2 w (Ioo (0 : ℝ) v) :=
    hw_smooth.mono hSubset
  have hRange : ∀ y ∈ Ico u v, 0 < y ∧ ENNReal.ofReal y < C := by
    intro y hy
    exact hSubset ⟨lt_of_lt_of_le hu hy.1, hy.2⟩
  have hDeriv : ∀ y ∈ Ico u v, 0 ≤ deriv w y := by
    intro y hy
    have hd := hw_grad y (hRange y hy).1 (hRange y hy).2
    linarith
  have hRewardBound :=
    avram_mix_fin26_original_reward_nonnegative_below_interior
      C hC w hw0 hw_cont hw_neg hw_smooth hw_grad
      v (lt_trans hu huv) hvC
  have hReward : ∀ y ∈ Ico u v, ∀ t : ℝ, t ≤ y → 0 ≤ w t := by
    intro y hy t ht
    exact hRewardBound t (le_trans ht (le_of_lt hy.2))
  have hUpper :=
    avram_mix_fin26_original_reward_upper_by_interior_cap
      C hC w hw_cont hw_smooth hw_grad u v hu huv hvC
  have hHJB : ∀ y ∈ Ico u v,
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0 := by
    intro y hy
    exact hw_gen y (hRange y hy).1 (hRange y hy).2
  have hQ : 0 ≤ q + (X.ν (Iio (0 : ℝ))).toReal := by
    have hnonneg : 0 ≤ (X.ν (Iio (0 : ℝ))).toReal :=
      ENNReal.toReal_nonneg
    linarith
  exact avram_mix_fin26_original_finite_cap_derivative_uniform
    X w q (X.ν (Iio (0 : ℝ))).toReal (w v) u v β ε
    hu huv hβ hε hA hFinite rfl hQ hSmooth hDeriv
    hReward hUpper hHJB hBeta hEps
