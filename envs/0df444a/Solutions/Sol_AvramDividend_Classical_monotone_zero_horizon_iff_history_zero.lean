-- Prove2me | solution 1 for AvramDividend.Classical.monotone_zero_horizon_iff_history_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:48:07.228534+00:00
-- url     : https://prove2.me/submissions/304e0fde-1c41-4495-8895-10f0a4e29422

import Mathlib.Data.NNReal.Basic
import Mathlib.Order.Monotone.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped NNReal

/-- For a monotone path starting at zero, zero at the horizon means zero throughout the past. -/
theorem solution (Y : ℝ≥0 → ℝ) (hMono : Monotone Y)
    (hZero : Y 0 = 0) (t : ℝ≥0) :
    Y t = 0 ↔ ∀ s : ℝ≥0, s ≤ t → Y s = 0 := by
  constructor
  · intro ht s hs
    have h0 := hMono (show (0 : ℝ≥0) ≤ s from bot_le)
    have hst := hMono hs
    rw [hZero] at h0
    rw [ht] at hst
    exact le_antisymm hst h0
  · intro h
    exact h t le_rfl
