-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_jump8_halfopen_marked_lintegral_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T13:37:35.500473+00:00
-- url     : https://prove2.me/submissions/d06ba940-529b-408f-a906-335be23115ad

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

/-- A nonnegative marked integrand splits over adjacent half-open time windows. -/
theorem solution
    (μ : Measure (ℝ≥0 × ℝ))
    (g : ℝ≥0 × ℝ → ℝ≥0∞) (hg : Measurable g)
    (s t : ℝ≥0) (hst : s ≤ t) :
    (∫⁻ p : ℝ≥0 × ℝ, if 0 < p.1 ∧ p.1 ≤ t then g p else 0 ∂μ) =
      (∫⁻ p : ℝ≥0 × ℝ, if 0 < p.1 ∧ p.1 ≤ s then g p else 0 ∂μ) +
      (∫⁻ p : ℝ≥0 × ℝ, if s < p.1 ∧ p.1 ≤ t then g p else 0 ∂μ) := by
  let f : ℝ≥0 × ℝ → ℝ≥0∞ := fun p =>
    if 0 < p.1 ∧ p.1 ≤ s then g p else 0
  let h : ℝ≥0 × ℝ → ℝ≥0∞ := fun p =>
    if s < p.1 ∧ p.1 ≤ t then g p else 0
  have hf : Measurable f := by
    dsimp [f]
    have hmask : MeasurableSet
        {p : ℝ≥0 × ℝ | 0 < p.1 ∧ p.1 ≤ s} := by
      change MeasurableSet
        ((fun p : ℝ≥0 × ℝ => p.1) ⁻¹' Ioc (0 : ℝ≥0) s)
      exact measurableSet_Ioc.preimage measurable_fst
    exact Measurable.ite hmask hg measurable_const
  have heq (p : ℝ≥0 × ℝ) :
      (if 0 < p.1 ∧ p.1 ≤ t then g p else 0) = f p + h p := by
    by_cases hp : 0 < p.1
    · by_cases hs : p.1 ≤ s
      · have ht : p.1 ≤ t := le_trans hs hst
        have hn : ¬ s < p.1 := not_lt_of_ge hs
        simp [f, h, hp, hs, ht, hn]
      · have hs' : s < p.1 := lt_of_not_ge hs
        by_cases ht : p.1 ≤ t
        · simp [f, h, hp, hs, hs', ht]
        · simp [f, h, hp, hs, hs', ht]
    · have h0s : (0 : ℝ≥0) ≤ s := zero_le
      have hn : ¬ s < p.1 :=
        not_lt_of_ge (le_trans (le_of_not_gt hp) h0s)
      simp [f, h, hp, hn]
  calc
    (∫⁻ p : ℝ≥0 × ℝ, if 0 < p.1 ∧ p.1 ≤ t then g p else 0 ∂μ) =
        (∫⁻ p : ℝ≥0 × ℝ, f p + h p ∂μ) := by
      congr 1
      funext p
      exact heq p
    _ = (∫⁻ p : ℝ≥0 × ℝ, f p ∂μ) +
          (∫⁻ p : ℝ≥0 × ℝ, h p ∂μ) :=
      MeasureTheory.lintegral_add_left hf h
    _ = _ := rfl
