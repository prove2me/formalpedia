-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_jump8_strict_cutoff_closed_band_exhaustion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T13:39:27.700488+00:00
-- url     : https://prove2.me/submissions/8ec3be66-969d-4f2e-99a1-fce1553d482a

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

noncomputable section

/-- A strict cutoff is an increasing union of closed negative-mark bands. -/
theorem solution (ε y : ℝ) (hε : 0 < ε) :
    y < -ε ↔ ∃ n : ℕ, y ≤ -ε - 1 / ((n : ℝ) + 1) := by
  constructor
  · intro hy
    have hgap : 0 < -ε - y := by linarith
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hgap
    refine ⟨n, ?_⟩
    linarith
  · rintro ⟨n, hn⟩
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith
