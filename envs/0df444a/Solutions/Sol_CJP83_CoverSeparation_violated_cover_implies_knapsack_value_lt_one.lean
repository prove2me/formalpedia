-- Prove2me | solution 1 for CJP83.CoverSeparation.violated_cover_implies_knapsack_value_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-08T02:35:20.576224+00:00
-- url     : https://prove2.me/submissions/7e90005f-5d23-42e5-8c0c-fe5b7c89e756

import Mathlib
import Definitions.Def_CJP83_CoverSeparation_KnapsackRow

open CJP83.CoverSeparation
open scoped BigOperators

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℚ) (a₀ : ℚ) (hpos : ∀ j, 0 < a j)
    (xbar : ι → ℝ) (z : ℝ) (hz : IsLeast (sepValues a a₀ xbar) z)
    (S : Finset ι) (hcover : IsMinimalCover a a₀ S)
    (hviolated : (S.card : ℝ) - 1 < ∑ j ∈ S, xbar j) : z < 1 := by
  have hzle := hz.2 (show (∑ j ∈ S, (1 - xbar j)) ∈ sepValues a a₀ xbar from
    ⟨S, hcover.1, rfl⟩)
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one] at hzle
  linarith
