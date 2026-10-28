-- Prove2me | solution 1 for AvramDividend.Classical.reflected_excursion_exceeds_hit_height_of_local_negative_increments
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:21:09.622449+00:00
-- url     : https://prove2.me/submissions/4e64b5fe-97a2-492f-ad7c-62b011052a8d

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
    (hNeg : ∀ ε : ℝ≥0, 0 < ε →
      ∃ s : ℝ≥0, s < ε ∧ Y (T + s) < Y T) :
    ∃ t : ℝ≥0, T ≤ t ∧ t < ζ ∧ (x : ℝ) < S t - Y t := by
  have hε : (0 : ℝ≥0) < ζ - T := tsub_pos_iff_lt.mpr hT
  obtain ⟨s, hs, hY⟩ := hNeg (ζ - T) hε
  have hTle : T ≤ T + s :=
    le_add_of_nonneg_right (bot_le : (0 : ℝ≥0) ≤ s)
  refine ⟨T + s, hTle, ?_, ?_⟩
  · have hsum : T + (ζ - T) = ζ := add_tsub_cancel_of_le (le_of_lt hT)
    calc
      T + s < T + (ζ - T) := by
        simpa [add_comm] using (add_lt_add_left hs T)
      _ = ζ := hsum
  · have hSle : S T ≤ S (T + s) := hS hTle
    linarith
