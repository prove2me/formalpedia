-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_i_moment_global_poly_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T18:27:30.305532+00:00
-- url     : https://prove2.me/submissions/7123aa36-fe16-4afa-90ec-41639e7502b6

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology

theorem solution
    (g : ℝ → ℝ) (p : Polynomial ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (K : ℕ) (hg0 : ∀ z : ℝ, 1 ≤ z → g z = 0)
    (happrox : ∀ z ∈ Set.Icc (0 : ℝ) 2, |p.eval z - g z| ≤ ε)
    (htail : ∀ z : ℝ, 2 ≤ z → |p.eval z| ≤ ε * z ^ K) :
    ∀ z : ℝ, 0 ≤ z →
      |g z - p.eval z| ≤ ε * (1 + z ^ K) := by
  intro z hz
  have hzk : 0 ≤ z ^ K := pow_nonneg hz K
  by_cases h2 : z ≤ 2
  · have hap := happrox z ⟨hz, h2⟩
    rw [abs_sub_comm]
    nlinarith [mul_nonneg hε hzk]
  · have hhigh : 2 ≤ z := by linarith
    have hz1 : 1 ≤ z := by linarith
    have hg : g z = 0 := hg0 z hz1
    have hp := htail z hhigh
    rw [hg, zero_sub, abs_neg]
    nlinarith [mul_nonneg hε hzk]
