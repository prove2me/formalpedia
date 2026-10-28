-- Prove2me | solution 1 for AvramDividend.Classical.bv_binomial_pattern_sum_ws01b
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T00:20:56.516293+00:00
-- url     : https://prove2.me/submissions/0a32993e-d7d7-4a02-80d8-2ca6acf07b63

import Mathlib

open Finset
open scoped BigOperators

theorem solution
    (n k : ℕ) (p q : ℝ) :
    (∑ S ∈ Finset.powersetCard k (Finset.range n),
      ∏ i ∈ Finset.range n, if i ∈ S then p else q) =
        (Nat.choose n k : ℝ) * p ^ k * q ^ (n - k) := by
  have key : ∀ S ∈ Finset.powersetCard k (Finset.range n),
      (∏ i ∈ Finset.range n, if i ∈ S then p else q) = p ^ k * q ^ (n - k) := by
    intro S hS
    rw [Finset.mem_powersetCard] at hS
    obtain ⟨hsub, hcard⟩ := hS
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
    have h1 : (Finset.range n).filter (fun i => i ∈ S) = S := by
      ext i; simp only [Finset.mem_filter]; constructor
      · exact fun h => h.2
      · exact fun h => ⟨hsub h, h⟩
    have h2 : ((Finset.range n).filter (fun i => ¬ i ∈ S)).card = n - k := by
      rw [Finset.filter_not, Finset.card_sdiff, h1, Finset.inter_eq_left.mpr hsub, hcard,
        Finset.card_range]
    rw [h1, hcard, h2]
  rw [Finset.sum_congr rfl key, Finset.sum_const, Finset.card_powersetCard, Finset.card_range,
    nsmul_eq_mul, mul_assoc]
