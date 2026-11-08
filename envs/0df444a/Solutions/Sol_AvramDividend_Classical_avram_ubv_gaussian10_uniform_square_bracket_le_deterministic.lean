-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gaussian10_uniform_square_bracket_le_deterministic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T12:46:53.102387+00:00
-- url     : https://prove2.me/submissions/bf4e64c5-5f9a-4756-a6de-5c89dd7d246a

import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

/-- The Gaussian square-energy bracket admits an all-path deterministic cap. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (H : ℝ≥0 × Ω → ℝ)
    (μtime : Measure ℝ≥0) (T : ℝ≥0)
    (hFinite : μtime (Ioc (0 : ℝ≥0) T) < ⊤)
    (C : ℝ) (hC : 0 ≤ C)
    (hBound : ∀ p, |H p| ≤ C) :
    ∀ ω, (∫ t in Ioc (0 : ℝ≥0) T,
      (H (t, ω)) ^ 2 ∂μtime) ≤
      C ^ 2 * (μtime.restrict (Ioc (0 : ℝ≥0) T)).real Set.univ := by
  letI : IsFiniteMeasure (μtime.restrict (Ioc (0 : ℝ≥0) T)) :=
    (isFiniteMeasure_restrict).2 hFinite.ne
  intro ω
  calc
    (∫ t in Ioc (0 : ℝ≥0) T, (H (t, ω)) ^ 2 ∂μtime)
        ≤ |∫ t in Ioc (0 : ℝ≥0) T, (H (t, ω)) ^ 2 ∂μtime| :=
            le_abs_self _
    _ = ‖∫ t in Ioc (0 : ℝ≥0) T, (H (t, ω)) ^ 2 ∂μtime‖ :=
          (Real.norm_eq_abs _).symm
    _ ≤ C ^ 2 * (μtime.restrict (Ioc (0 : ℝ≥0) T)).real Set.univ := by
      apply norm_integral_le_of_norm_le_const
      filter_upwards [] with t
      have h0 := abs_nonneg (H (t, ω))
      have h1 := hBound (t, ω)
      have h2 : 0 ≤ C - |H (t, ω)| := sub_nonneg.mpr h1
      have h3 : 0 ≤ C + |H (t, ω)| := add_nonneg hC h0
      have hh := mul_nonneg h2 h3
      simp only [Real.norm_eq_abs, abs_pow]
      nlinarith
