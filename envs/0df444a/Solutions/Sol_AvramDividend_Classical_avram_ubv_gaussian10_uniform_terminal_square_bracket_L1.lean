-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gaussian10_uniform_terminal_square_bracket_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T12:22:14.898149+00:00
-- url     : https://prove2.me/submissions/41058343-f1aa-498c-b412-46fff406c8ed

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

/-- A finite-horizon Gaussian energy bracket with a uniform source bound is L¹. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P]
    (H : ℝ≥0 × Ω → ℝ)
    (μtime : Measure ℝ≥0) (T : ℝ≥0)
    (hFinite : μtime (Ioc (0 : ℝ≥0) T) < ⊤)
    (C : ℝ) (hC : 0 ≤ C)
    (hBound : ∀ p, |H p| ≤ C)
    (hTerminalMeas : Measurable (fun ω =>
      ∫ t in Ioc (0 : ℝ≥0) T, (H (t, ω)) ^ 2 ∂μtime)) :
    Integrable (fun ω => ∫ t in Ioc (0 : ℝ≥0) T,
      (H (t, ω)) ^ 2 ∂μtime) P := by
  letI : IsFiniteMeasure (μtime.restrict (Ioc (0 : ℝ≥0) T)) :=
    (isFiniteMeasure_restrict).2 hFinite.ne
  apply Integrable.of_bound hTerminalMeas.aestronglyMeasurable
    ((C ^ 2) * (μtime.restrict (Ioc (0 : ℝ≥0) T)).real Set.univ)
  filter_upwards [] with ω
  apply norm_integral_le_of_norm_le_const
  filter_upwards [] with t
  have h0 := abs_nonneg (H (t, ω))
  have h1 := hBound (t, ω)
  have h2 : 0 ≤ C - |H (t, ω)| := sub_nonneg.mpr h1
  have h3 : 0 ≤ C + |H (t, ω)| := add_nonneg hC h0
  have hh := mul_nonneg h2 h3
  simp only [Real.norm_eq_abs, abs_pow]
  nlinarith
