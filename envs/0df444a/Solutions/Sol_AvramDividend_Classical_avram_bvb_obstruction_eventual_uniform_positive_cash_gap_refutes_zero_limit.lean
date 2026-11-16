-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_obstruction_eventual_uniform_positive_cash_gap_refutes_zero_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T07:47:28.537747+00:00
-- url     : https://prove2.me/submissions/6d6e7af9-fdff-49be-a252-e0fc14485f04

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Set
open scoped Topology
theorem solution (A : ℕ → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hLower : ∀ n, 4 ≤ n → ε ≤ A n) :
    ¬ Tendsto (fun n => max (A n) 0) atTop (𝓝 (0 : ℝ)) := by
  intro hLimit
  have hSmall : ∀ᶠ n : ℕ in atTop, max (A n) 0 < ε := by
    exact hLimit.eventually (isOpen_Iio.mem_nhds hε)
  have hLarge : ∀ᶠ n : ℕ in atTop, 4 ≤ n :=
    eventually_ge_atTop 4
  obtain ⟨n, hSmallN, hLargeN⟩ :=
    (hSmall.and hLarge).exists
  have hBound := hLower n hLargeN
  have hMax : A n ≤ max (A n) 0 := le_max_left _ _
  linarith
