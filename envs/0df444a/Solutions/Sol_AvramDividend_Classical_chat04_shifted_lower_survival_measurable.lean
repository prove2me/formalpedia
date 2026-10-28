-- Prove2me | solution 1 for AvramDividend.Classical.chat04_shifted_lower_survival_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T14:37:44.353521+00:00
-- url     : https://prove2.me/submissions/4027b948-d193-497e-83c9-cff182368a85

import Theorems.Thm_AvramDividend_Classical_chat03_lower_survival_filtration_measurable
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal

/-- Closed-horizon nonruin of the reserve shifted by x is measurable,
using the countable-grid filtration theorem. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : ℕ → ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (x : ℝ) (t : ℝ≥0) :
    MeasurableSet {ω | ∀ s : ℝ≥0,
      s ≤ t → 0 ≤ x + X.X s ω} := by
  have hFil := chat03_lower_survival_filtration_measurable
    X τ hCover (-x) t
  have hMeas : MeasurableSet {ω | ∀ s : ℝ≥0,
      s ≤ t → ¬ X.X s ω < -x} :=
    (𝓕.le t) _ hFil
  convert hMeas using 1
  ext ω
  simp only [Set.mem_setOf_eq]
  constructor
  · intro h s hs
    have hh := h s hs
    linarith
  · intro h s hs
    have hh := h s hs
    linarith