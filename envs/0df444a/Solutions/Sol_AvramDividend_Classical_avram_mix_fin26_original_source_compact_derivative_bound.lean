-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_fin26_original_source_compact_derivative_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T14:26:28.354419+00:00
-- url     : https://prove2.me/submissions/7a2e0f2a-7bd2-4852-8186-36b99db51502

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin26_original_source_compact_derivative_uniform
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
    ∃ B : ℝ, ∀ y ∈ Ico u v, deriv w y ≤ B := by
  have hσsq : 0 < X.σ ^ 2 := sq_pos_of_ne_zero hσ
  have ha : 0 < X.σ ^ 2 / 2 := by nlinarith
  let a : ℝ := X.σ ^ 2 / 2
  let d : ℝ := (q + (X.ν (Iio (0 : ℝ))).toReal) * w v
  let β : ℝ := max 0 (-X.c / a)
  let ε : ℝ := max 0 (d / a)
  have hβ : 0 ≤ β := le_max_left _ _
  have hε : 0 ≤ ε := le_max_left _ _
  have hane : a ≠ 0 := ne_of_gt ha
  have hbetaBound : -X.c ≤ a * β := by
    have hle : -X.c / a ≤ β := le_max_right _ _
    have hmul := mul_le_mul_of_nonneg_left hle (le_of_lt ha)
    have hcancel : a * (-X.c / a) = -X.c := by
      field_simp [hane]
    calc
      -X.c = a * (-X.c / a) := hcancel.symm
      _ ≤ a * β := hmul
  have hepsBound : d ≤ a * ε := by
    have hle : d / a ≤ ε := le_max_right _ _
    have hmul := mul_le_mul_of_nonneg_left hle (le_of_lt ha)
    have hcancel : a * (d / a) = d := by
      field_simp [hane]
    calc
      d = a * (d / a) := hcancel.symm
      _ ≤ a * ε := hmul
  have hFinite : X.ν (Iio (0 : ℝ)) < ⊤ :=
    lt_top_iff_ne_top.mpr hFiniteActivity
  exact avram_mix_fin26_original_source_compact_derivative_uniform
    X w C hC q u v β ε hq hu huv hvC
    hβ hε ha hFinite hw0 hw_cont hw_neg hw_smooth
    hw_gen hw_grad (by simpa [a] using hbetaBound)
    (by simpa [a, d] using hepsBound)
