-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid4_finite_cap_band_eventually_contains_interior_reserve
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T07:03:45.472124+00:00
-- url     : https://prove2.me/submissions/7643a647-493d-4361-87b5-b0dff64b3df3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
noncomputable section

/-- The explicitly refining finite-cap reserve band eventually covers each strict interior reserve. -/
theorem solution (c d y : ℝ) (hc : 0 < c) (hd : 0 < d)
    (hy : 0 < y) (hyc : y < c) :
    ∃ N : ℕ, ∀ n ≥ N,
      y ∈ Icc ((d / ((n : ℝ) + 1)) / 2)
        (c * ((n : ℝ) + 1) / ((n : ℝ) + 2)) := by
  have hgap : 0 < c - y := by linarith
  obtain ⟨N, hN⟩ :=
    exists_nat_gt (max (d / (2 * y)) ((2 * y - c) / (c - y)))
  refine ⟨N, ?_⟩
  intro n hn
  have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hL : d / (2 * y) < (n : ℝ) + 1 := by
    have h := lt_of_le_of_lt
      (le_max_left (d / (2 * y)) ((2 * y - c) / (c - y))) hN
    linarith
  have hU : (2 * y - c) / (c - y) < (n : ℝ) := by
    have h := lt_of_le_of_lt
      (le_max_right (d / (2 * y)) ((2 * y - c) / (c - y))) hN
    linarith
  have hlow : d < ((n : ℝ) + 1) * (2 * y) :=
    (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * y)).1 hL
  have hupp : 2 * y - c < ((n : ℝ) * (c - y)) :=
    (div_lt_iff₀ hgap).1 hU
  constructor
  · change d / ((n : ℝ) + 1) / 2 ≤ y
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)).2
    nlinarith
  · change y ≤ c * ((n : ℝ) + 1) / ((n : ℝ) + 2)
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < ((n : ℝ) + 2))).2
    nlinarith
