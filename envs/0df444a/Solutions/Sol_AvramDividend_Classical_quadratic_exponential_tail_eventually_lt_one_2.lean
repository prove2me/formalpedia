-- Prove2me | solution 2 for AvramDividend.Classical.quadratic_exponential_tail_eventually_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-10-06T18:00:53.07317+00:00
-- url     : https://prove2.me/submissions/9cdb7405-57bd-4e9e-8f8b-35761710cf13

import Mathlib
open Filter

theorem solution
    (a β0 C K : ℝ) (ha : 0 < a) :
    ∃ β : ℝ, β0 ≤ β ∧
      C * (1 + β ^ 2) *
        (Real.exp (-(β - β0) * a) * K) < 1 := by
  have h0 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 a ha
  have h2 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 a ha
  have h := ((h0.add h2).const_mul (C * K * Real.exp (β0 * a)))
  rw [add_zero, mul_zero] at h
  obtain ⟨β, hβ⟩ := ((h.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))).and
    (eventually_ge_atTop (max β0 0))).exists
  refine ⟨β, le_trans (le_max_left _ _) hβ.2, ?_⟩
  have hb0 : 0 ≤ β := le_trans (le_max_right _ _) hβ.2
  have e1 : Real.exp (-(β - β0) * a) = Real.exp (β0 * a) * Real.exp (-a * β) := by
    rw [← Real.exp_add]; ring_nf
  have := hβ.1
  rw [Real.rpow_zero, Real.rpow_two] at this
  rw [e1]
  calc C * (1 + β ^ 2) * (Real.exp (β0 * a) * Real.exp (-a * β) * K)
      = C * K * Real.exp (β0 * a) * (1 * Real.exp (-a * β) + β ^ 2 * Real.exp (-a * β)) := by ring
    _ < 1 := this
