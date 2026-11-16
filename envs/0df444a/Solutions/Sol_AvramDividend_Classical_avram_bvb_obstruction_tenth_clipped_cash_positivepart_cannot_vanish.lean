-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_obstruction_tenth_clipped_cash_positivepart_cannot_vanish
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T07:55:46.469072+00:00
-- url     : https://prove2.me/submissions/7e3c27e4-1290-4bd0-9e1d-49bcda32b7e3

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_eventual_uniform_positive_cash_gap_refutes_zero_limit
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_tenth_clipped_cash_terminal_minimum_exceeds_half
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Real AvramDividend.Classical
open scoped Topology
theorem solution
    (F L : ℕ → ℝ)
    (hF : ∀ n, 4 ≤ n →
      (2 / 25 + 1 / 2 : ℝ) * Real.exp (-(1 / 10 : ℝ)) ≤ F n)
    (hL : ∀ n, L n = 0) :
    ¬ Tendsto (fun n => max (F n - ((1 / 2 : ℝ) + L n)) 0)
      atTop (𝓝 (0 : ℝ)) := by
  let ε : ℝ :=
    (2 / 25 + 1 / 2 : ℝ) * Real.exp (-(1 / 10 : ℝ)) - 1 / 2
  have hε : 0 < ε := by
    dsimp [ε]
    have hGap :=
      avram_bvb_obstruction_tenth_clipped_cash_terminal_minimum_exceeds_half
    linarith
  have hLower : ∀ n, 4 ≤ n →
      ε ≤ F n - ((1 / 2 : ℝ) + L n) := by
    intro n hn
    rw [hL n]
    dsimp [ε]
    have h := hF n hn
    linarith
  exact avram_bvb_obstruction_eventual_uniform_positive_cash_gap_refutes_zero_limit
    (fun n => F n - ((1 / 2 : ℝ) + L n)) ε hε hLower
