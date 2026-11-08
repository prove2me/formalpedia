-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gaussian10_uniform_source_square_energy_integrableOn
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T12:18:43.614949+00:00
-- url     : https://prove2.me/submissions/07e86d18-4907-4dfd-9f4c-75092e37ed27

import Mathlib.MeasureTheory.Integral.IntegrableOn

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

/-- Uniform original-source bounds give pathwise finite-horizon square energy. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (H : ℝ≥0 × Ω → ℝ)
    (hH : ∀ ω, Measurable (fun t : ℝ≥0 => H (t, ω)))
    (μtime : Measure ℝ≥0) (T : ℝ≥0)
    (hFinite : μtime (Ioc (0 : ℝ≥0) T) < ⊤)
    (C : ℝ) (hC : 0 ≤ C)
    (hBound : ∀ p, |H p| ≤ C) :
    ∀ ω, IntegrableOn (fun t : ℝ≥0 => (H (t, ω)) ^ 2)
      (Ioc (0 : ℝ≥0) T) μtime := by
  intro ω
  apply IntegrableOn.of_bound hFinite
    (((hH ω).pow_const 2).aestronglyMeasurable) (C ^ 2)
  filter_upwards [] with t
  have h0 := abs_nonneg (H (t, ω))
  have h1 := hBound (t, ω)
  have h2 : 0 ≤ C - |H (t, ω)| := sub_nonneg.mpr h1
  have h3 : 0 ≤ C + |H (t, ω)| := add_nonneg hC h0
  have hh := mul_nonneg h2 h3
  simp only [Real.norm_eq_abs, abs_pow]
  nlinarith
