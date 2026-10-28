-- Prove2me | solution 1 for AvramDividend.Classical.reflected_excursion_height_max_forces_no_immediate_negative_increments
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:27:33.495987+00:00
-- url     : https://prove2.me/submissions/0155a763-47db-491b-9037-ee35880ae32a

import Mathlib.Data.NNReal.Defs
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped NNReal

theorem solution
    (S Y : ℝ≥0 → ℝ) (T ζ x : ℝ≥0)
    (hT : T < ζ)
    (hS : Monotone S)
    (hHit : S T - Y T = (x : ℝ))
    (hNoExceed : ∀ t : ℝ≥0, T ≤ t → t < ζ →
      S t - Y t ≤ (x : ℝ)) :
    ∃ ε : ℝ≥0, 0 < ε ∧
      ∀ s : ℝ≥0, s < ε → Y T ≤ Y (T + s) := by
  have hε : (0 : ℝ≥0) < ζ - T := tsub_pos_iff_lt.mpr hT
  refine ⟨ζ - T, hε, ?_⟩
  intro s hs
  have hTle : T ≤ T + s :=
    le_add_of_nonneg_right (bot_le : (0 : ℝ≥0) ≤ s)
  have hTlt : T + s < ζ := by
    calc
      T + s < T + (ζ - T) := by
        simpa [add_comm] using (add_lt_add_left hs T)
      _ = ζ := add_tsub_cancel_of_le (le_of_lt hT)
  have hmax := hNoExceed (T + s) hTle hTlt
  have hSle := hS hTle
  linarith
