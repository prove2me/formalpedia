-- Prove2me | solution 1 for AvramDividend.Classical.positive_tilted_of_exponential_cumulative_measure
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T02:58:20.286786+00:00
-- url     : https://prove2.me/submissions/bb3504c1-1cc3-41a1-b598-aca9385ef3b2

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

open MeasureTheory Set in
theorem solution (β : Measure ℝ) (φ : ℝ) (hφ : 0 < φ)
    (hfin : ∀ x : ℝ, 0 < x → β (Iic x) ≠ ⊤)
    (hatom : 0 < β {0})
    (W : ℝ → ℝ)
    (hW : ∀ x : ℝ, 0 < x →
      W x = Real.exp (φ * x) * (β (Iic x)).toReal) :
    (∀ x : ℝ, 0 < x → 0 < W x) ∧
      MonotoneOn (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0) := by
  have key : ∀ x : ℝ, 0 < x → Real.exp (-φ * x) * W x = (β (Iic x)).toReal := by
    intro x hx
    rw [hW x hx, ← mul_assoc, ← Real.exp_add]
    have : -φ * x + φ * x = 0 := by ring
    rw [this, Real.exp_zero, one_mul]
  refine ⟨?_, ?_⟩
  · intro x hx
    rw [hW x hx]
    apply mul_pos (Real.exp_pos _)
    apply ENNReal.toReal_pos
    · apply ne_of_gt
      exact lt_of_lt_of_le hatom (measure_mono (by
        intro y hy
        rw [mem_singleton_iff] at hy
        rw [mem_Iic, hy]
        exact hx.le))
    · exact hfin x hx
  · intro a ha b hb hab
    simp only
    rw [key a ha, key b hb]
    exact ENNReal.toReal_mono (hfin b hb) (measure_mono (Iic_subset_Iic.mpr hab))
