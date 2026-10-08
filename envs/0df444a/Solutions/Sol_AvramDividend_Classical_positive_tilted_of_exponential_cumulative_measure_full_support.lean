-- Prove2me | solution 1 for AvramDividend.Classical.positive_tilted_of_exponential_cumulative_measure_full_support
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T23:26:21.958068+00:00
-- url     : https://prove2.me/submissions/00646114-8684-4e84-bead-47108f6dfdc3

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

/-- Cumulative mass positive on each positive half-line replaces a
positive atom at zero in the unbounded-variation renewal representation. -/
theorem solution (β : Measure ℝ) (φ : ℝ) (hφ : 0 < φ)
    (hfin : ∀ x : ℝ, 0 < x → β (Iic x) ≠ ⊤)
    (hmass : ∀ x : ℝ, 0 < x → 0 < β (Iic x))
    (W : ℝ → ℝ)
    (hW : ∀ x : ℝ, 0 < x →
      W x = Real.exp (φ * x) * (β (Iic x)).toReal) :
    (∀ x : ℝ, 0 < x → 0 < W x) ∧
      MonotoneOn (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0) := by
  have key : ∀ x : ℝ, 0 < x →
      Real.exp (-φ * x) * W x = (β (Iic x)).toReal := by
    intro x hx
    rw [hW x hx, ← mul_assoc, ← Real.exp_add]
    have hcancel : -φ * x + φ * x = 0 := by ring
    rw [hcancel, Real.exp_zero, one_mul]
  refine ⟨?_, ?_⟩
  · intro x hx
    rw [hW x hx]
    apply mul_pos (by positivity)
    apply ENNReal.toReal_pos
    · exact ne_of_gt (hmass x hx)
    · exact hfin x hx
  · intro a ha b hb hab
    simp only
    rw [key a ha, key b hb]
    exact ENNReal.toReal_mono (hfin b hb)
      (measure_mono (Iic_subset_Iic.mpr hab))
