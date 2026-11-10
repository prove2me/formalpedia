-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_gauss14_generic_negative_mark_window_integral_formula
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T11:15:53.439939+00:00
-- url     : https://prove2.me/submissions/3a1590ea-1b1b-4148-99a3-f2241054ac93

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_negative_integral_eq_neg_lintegral_toReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Exact signed negative-mark window integral as a nonnegative weighted mass. -/
theorem solution (μ : Measure (ℝ≥0 × ℝ))
    (a b : ℝ≥0) (B : Set ℝ) [DecidablePred (· ∈ B)] (hB : MeasurableSet B)
    (hNeg : ∀ z ∈ B, z ≤ 0) :
    (∫ p in (Ioc a b ×ˢ B), p.2 ∂μ) =
      -((∫⁻ p : ℝ≥0 × ℝ,
        if a < p.1 ∧ p.1 ≤ b then
          (if p.2 ∈ B then ENNReal.ofReal (-p.2) else 0) else 0 ∂μ).toReal) := by
  classical
  let S : Set (ℝ≥0 × ℝ) := Ioc a b ×ˢ B
  have hS : MeasurableSet S := measurableSet_Ioc.prod hB
  have heq := avram_mix_gauss14_negative_integral_eq_neg_lintegral_toReal
    μ S hS (fun p : ℝ≥0 × ℝ => p.2) measurable_snd
    (by intro p hp; exact hNeg p.2 hp.2)
  rw [heq]
  congr 1
  rw [← lintegral_indicator hS]
  congr 1
  apply lintegral_congr
  intro p
  by_cases ht : a < p.1 ∧ p.1 ≤ b
  · by_cases hb : p.2 ∈ B
    · simp [S, Set.indicator, Set.mem_prod, Set.mem_Ioc, ht, hb]
    · simp [S, Set.indicator, Set.mem_prod, Set.mem_Ioc, ht, hb]
  · simp [S, Set.indicator, Set.mem_prod, Set.mem_Ioc, ht]
