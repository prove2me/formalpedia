-- Prove2me | solution 1 for AvramDividend.Classical.avram_f16_original_positive_gaussian_compact_C2_discount_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T00:19:48.710144+00:00
-- url     : https://prove2.me/submissions/b349d584-5cd5-44d8-8140-f5c1935d1967

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_source_interior_compact_derivative_bound
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_compact_discounted_hessian_uniform_bound
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hσ : 0 < X.σ)
    (q : ℝ) (hq : 0 ≤ q) (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hopen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hband : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    ∃ KG KH : ℝ, 0 ≤ KG ∧ 0 ≤ KH ∧
      (∀ (t : ℝ≥0) (y : ℝ), y ∈ Icc a b →
        |Real.exp (-(q * (t : ℝ))) * deriv w y| ≤ KG) ∧
      (∀ (t : ℝ≥0) (y : ℝ), y ∈ Icc a b →
        |Real.exp (-(q * (t : ℝ))) * iteratedDeriv 2 w y| ≤ KH) := by
  obtain ⟨Bg, hBg⟩ :=
    avram_p4_f3_source_interior_compact_derivative_bound
      w C hw hopen a b hband
  obtain ⟨Bh, hBh, hBhBound⟩ :=
    avram_p4_a_gaussian_original_compact_discounted_hessian_uniform_bound
      X q hq C w hw a b hband
  let m : ℝ := X.σ ^ 2 / 2
  have hm : 0 < m := by
    dsimp only [m]
    exact div_pos (sq_pos_of_pos hσ) (by norm_num)
  let KG : ℝ := max Bg 0
  let KH : ℝ := Bh / m
  have hKG : 0 ≤ KG := le_max_right _ _
  have hKH : 0 ≤ KH := div_nonneg hBh hm.le
  refine ⟨KG, KH, hKG, hKH, ?_, ?_⟩
  · intro t y hy
    have ht : 0 ≤ (t : ℝ) := t.property
    have hqt : 0 ≤ q * (t : ℝ) := mul_nonneg hq ht
    have hExpLe : Real.exp (-(q * (t : ℝ))) ≤ 1 :=
      (Real.exp_le_one_iff).2 (neg_nonpos.mpr hqt)
    have hGrad := hBg y hy
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      Real.exp (-(q * (t : ℝ))) * |deriv w y| ≤
          1 * |deriv w y| := by
            exact mul_le_mul_of_nonneg_right hExpLe (abs_nonneg _)
      _ = |deriv w y| := one_mul _
      _ ≤ KG := le_trans hGrad (le_max_left _ _)
  · intro t y hy
    have hb := hBhBound t y hy
    have heq :
        Real.exp (-(q * (t : ℝ))) *
          (X.σ ^ 2 / 2 * iteratedDeriv 2 w y) =
        m * (Real.exp (-(q * (t : ℝ))) * iteratedDeriv 2 w y) := by
      dsimp only [m]
      ring
    rw [heq, abs_mul, abs_of_pos hm] at hb
    change |Real.exp (-(q * (t : ℝ))) * iteratedDeriv 2 w y| ≤ Bh / m
    apply (le_div_iff₀ hm).2
    simpa only [mul_comm] using hb
