-- Prove2me | solution 1 for AvramDividend.Classical.avram_a53_finite_causal_marked_jump_laplace_exp_eq_product_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T10:54:37.047286+00:00
-- url     : https://prove2.me/submissions/2d97ca31-eb8d-4414-8983-051bbfa16965

import Mathlib.Analysis.Complex.Exponential
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    (S : Finset ℝ≥0) (j : ℝ≥0 → ℝ)
    (t : ℝ≥0) (θ : ℝ) :
    Real.exp (θ * (∑ u ∈ S, if u ≤ t then j u else 0)) =
      ∏ u ∈ S, if u ≤ t then Real.exp (θ * j u) else 1 := by
  classical
  have hMul :
      θ * (∑ u ∈ S, if u ≤ t then j u else 0) =
        ∑ u ∈ S, if u ≤ t then θ * j u else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    split_ifs <;> ring
  rw [hMul, Real.exp_sum]
  apply Finset.prod_congr rfl
  intro u hu
  split_ifs <;> simp
