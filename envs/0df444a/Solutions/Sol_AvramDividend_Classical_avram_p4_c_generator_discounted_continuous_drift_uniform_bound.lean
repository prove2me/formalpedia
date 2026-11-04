-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_c_generator_discounted_continuous_drift_uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:23:12.659246+00:00
-- url     : https://prove2.me/submissions/173ff6eb-9b35-4111-b536-78c9f5b6671e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_compact_discounted_hessian_uniform_bound
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_compact_physical_drift_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Uniform original discounted Gaussian plus epsilon-physical drift bound,
with source C² assumptions only on the compact interior. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (q C u v ε : ℝ) (Cap : ℝ≥0∞)
    (hq : 0 ≤ q) (hε : 0 < ε)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hwCap : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < Cap})
    (hu : 0 < u) (hv : v < C)
    (hBand : Icc u v ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < Cap}) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ (t : ℝ≥0) (y : ℝ), y ∈ Icc u v →
      |Real.exp (-(q * (t : ℝ))) *
        (X.σ ^ 2 / 2 * iteratedDeriv 2 w y +
         (X.c - (∫ z in Ioo (-1 : ℝ) (-ε), z ∂X.ν)) * deriv w y)| ≤ M := by
  obtain ⟨K, hK0, hK⟩ :=
    avram_p4_a_gaussian_original_compact_discounted_hessian_uniform_bound
      X q hq Cap w hwCap u v hBand
  obtain ⟨_, B, hB⟩ :=
    avram_p4_c_generator_compact_physical_drift_bound
      X w C u v ε hw hu hv hε
  refine ⟨K + |B|, add_nonneg hK0 (abs_nonneg B), ?_⟩
  intro t y hy
  have ht : 0 ≤ (t : ℝ) := t.property
  have hqtime : -(q * (t : ℝ)) ≤ 0 :=
    neg_nonpos.mpr (mul_nonneg hq ht)
  have he : |Real.exp (-(q * (t : ℝ)))| ≤ 1 := by
    rw [abs_of_pos (Real.exp_pos _)]
    simpa only [Real.exp_zero] using (Real.exp_le_exp.mpr hqtime)
  have hD :
      |Real.exp (-(q * (t : ℝ))) *
        ((X.c - (∫ z in Ioo (-1 : ℝ) (-ε), z ∂X.ν)) * deriv w y)| ≤ |B| := by
    rw [abs_mul]
    calc
      |Real.exp (-(q * (t : ℝ)))| *
          |(X.c - ∫ z in Ioo (-1 : ℝ) (-ε), z ∂X.ν) * deriv w y|
          ≤ |Real.exp (-(q * (t : ℝ)))| * |B| :=
            mul_le_mul_of_nonneg_left ((hB y hy).trans (le_abs_self B)) (abs_nonneg _)
      _ ≤ 1 * |B| := mul_le_mul_of_nonneg_right he (abs_nonneg _)
      _ = |B| := one_mul _
  calc
    |Real.exp (-(q * (t : ℝ))) *
        (X.σ ^ 2 / 2 * iteratedDeriv 2 w y +
         (X.c - (∫ z in Ioo (-1 : ℝ) (-ε), z ∂X.ν)) * deriv w y)| =
        |Real.exp (-(q * (t : ℝ))) *
          (X.σ ^ 2 / 2 * iteratedDeriv 2 w y) +
         Real.exp (-(q * (t : ℝ))) *
          ((X.c - (∫ z in Ioo (-1 : ℝ) (-ε), z ∂X.ν)) * deriv w y)| := by
            rw [mul_add]
    _ ≤ |Real.exp (-(q * (t : ℝ))) *
          (X.σ ^ 2 / 2 * iteratedDeriv 2 w y)| +
        |Real.exp (-(q * (t : ℝ))) *
          ((X.c - (∫ z in Ioo (-1 : ℝ) (-ε), z ∂X.ν)) * deriv w y)| :=
          abs_add_le _ _
    _ ≤ K + |B| := add_le_add (hK t y hy) hD
