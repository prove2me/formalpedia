-- Prove2me | solution 1 for AvramDividend.Classical.bv_positive_shifted_increment_contact_right_interval_ws01c
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T23:05:12.316134+00:00
-- url     : https://prove2.me/submissions/40bae3cd-ef50-46b9-860c-34ea5eeffbde

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped NNReal

theorem solution
    (f : ℝ≥0 → ℝ) (τ : ℝ≥0) (barrier : ℝ)
    (hContact : f τ = barrier)
    (hPositive : ∃ ε : ℝ≥0, 0 < ε ∧
      ∀ h : ℝ≥0, 0 < h → h < ε →
        0 < f (τ + h) - f τ) :
    ∃ ε : ℝ≥0, 0 < ε ∧
      ∀ t : ℝ≥0, τ < t → t < τ + ε →
        barrier ≤ f t := by
  obtain ⟨ε, hεpos, hε⟩ := hPositive
  refine ⟨ε, hεpos, ?_⟩
  intro t hτt htε
  let h : ℝ≥0 := t - τ
  have hhpos : 0 < h := tsub_pos_iff_lt.mpr hτt
  have hDecomp : τ + h = t := by
    dsimp [h]
    exact add_tsub_cancel_of_le (le_of_lt hτt)
  have hhlt : h < ε := by
    rw [← hDecomp] at htε
    exact (add_lt_add_iff_left τ).mp htε
  have hInc := hε h hhpos hhlt
  rw [hDecomp, hContact] at hInc
  linarith