-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f3_original_strict_interior_small_jump_squared_kernel_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T16:46:14.679308+00:00
-- url     : https://prove2.me/submissions/09ac87bb-be20-4143-aa3b-584d09a37344

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_positive_band_lipschitz_source
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Physical small-jump squared kernels are bounded by quadratic source-mark energy on a strict interior band. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (δ K : ℝ) (hδ : 0 < δ) (hδK : δ ≤ K)
    (hK : ENNReal.ofReal K < C) :
    ∃ B0 : ℝ, 0 ≤ B0 ∧ ∀ u ∈ Icc δ K,
      ∀ B : Set ℝ, MeasurableSet B →
        (∀ z ∈ B, u + z ∈ Icc δ K) →
        (∫⁻ z in B, ENNReal.ofReal ((w (u + z) - w u) ^ 2) ∂X.ν) ≤
          (∫⁻ z in B, ENNReal.ofReal ((B0 * |z|) ^ 2) ∂X.ν) := by
  obtain ⟨L, hLip⟩ :=
    avram_p4_f3_original_positive_band_lipschitz_source
      w C hw_smooth δ K hδ hδK hK
  refine ⟨|L|, abs_nonneg _, ?_⟩
  intro u hu B hBmeas hB
  have hSq (z : ℝ) (hz : z ∈ B) :
      (w (u + z) - w u) ^ 2 ≤ (|L| * |z|) ^ 2 := by
    have huz : u + z ∈ Icc δ K := hB z hz
    have hL :
        |w (u + z) - w u| ≤ L * |z| := by
      simpa [add_sub_cancel_left] using hLip u hu (u + z) huz
    have hAbs :
        |w (u + z) - w u| ≤ |L| * |z| := calc
      _ ≤ L * |z| := hL
      _ ≤ |L| * |z| :=
        mul_le_mul_of_nonneg_right (le_abs_self L) (abs_nonneg z)
    have hLower := neg_le_of_abs_le hAbs
    have hUpper := le_of_abs_le hAbs
    have hPlus : 0 ≤ |L| * |z| + (w (u + z) - w u) := by linarith
    have hMinus : 0 ≤ |L| * |z| - (w (u + z) - w u) := by linarith
    nlinarith [mul_nonneg hPlus hMinus]
  refine lintegral_mono_ae ?_
  filter_upwards [ae_restrict_mem hBmeas] with z hz
  exact ENNReal.ofReal_le_ofReal (hSq z hz)
