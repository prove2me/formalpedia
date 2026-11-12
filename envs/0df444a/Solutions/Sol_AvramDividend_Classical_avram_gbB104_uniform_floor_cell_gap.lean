-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB104_uniform_floor_cell_gap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T22:36:12.878544+00:00
-- url     : https://prove2.me/submissions/b7e6a5b0-2489-45a2-bd62-1608d706c6c2

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology
noncomputable section

theorem solution
    (n m : ℕ) (hn : 0 < n) (t : ℝ) (ht : 0 ≤ t) :
    let Δ : ℝ := (n : ℝ) / ((m : ℝ) + 1)
    let i : ℕ := ⌊t / Δ⌋₊
    ((i : ℝ) * Δ ≤ t) ∧
      t - (i : ℝ) * Δ ≤ Δ := by
  intro Δ i
  have hΔ : 0 < Δ := by dsimp [Δ]; positivity
  have htdiv : 0 ≤ t / Δ := div_nonneg ht (le_of_lt hΔ)
  have hLo : (i : ℝ) ≤ t / Δ := Nat.floor_le htdiv
  have hHi : t / Δ < (i : ℝ) + 1 := Nat.lt_floor_add_one _
  constructor
  · exact (le_div_iff₀ hΔ).mp hLo
  · have hh : t < ((i : ℝ) + 1) * Δ :=
      (div_lt_iff₀ hΔ).mp hHi
    nlinarith
