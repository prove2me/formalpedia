-- Prove2me | solution 1 for AvramDividend.Classical.negative_before_horizon_iff_dense_grid_of_right_negative_persistence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:34:51.588261+00:00
-- url     : https://prove2.me/submissions/2ae39981-4ee7-430c-ac7d-e15f75ee804c

import Mathlib.Data.NNReal.Defs
import Mathlib.Topology.Order.OrderClosed

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped NNReal

theorem solution
    (times : ℕ → ℝ≥0)
    (hdense : ∀ a b : ℝ≥0, a < b →
      ∃ m : ℕ, a < times m ∧ times m < b)
    (f : ℝ≥0 → ℝ)
    (hnegOpen : ∀ t : ℝ≥0, f t < 0 →
      ∃ u : ℝ≥0, t < u ∧
        ∀ s : ℝ≥0, t ≤ s → s < u → f s < 0)
    (ε : ℝ≥0) :
    (∃ t : ℝ≥0, t < ε ∧ f t < 0) ↔
      (∃ m : ℕ, times m < ε ∧ f (times m) < 0) := by
  constructor
  · rintro ⟨t, htε, hneg⟩
    obtain ⟨u, htu, hu⟩ := hnegOpen t hneg
    have htmin : t < min u ε := lt_min htu htε
    obtain ⟨m, htm, hmb⟩ := hdense t (min u ε) htmin
    refine ⟨m, ?_, ?_⟩
    · exact lt_of_lt_of_le hmb (min_le_right u ε)
    · exact hu (times m) (le_of_lt htm)
        (lt_of_lt_of_le hmb (min_le_left u ε))
  · rintro ⟨m, hm, hneg⟩
    exact ⟨times m, hm, hneg⟩
