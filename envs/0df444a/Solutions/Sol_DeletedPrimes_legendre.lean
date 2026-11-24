-- Prove2me | solution 1 for DeletedPrimes.legendre
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:05:37.155898+00:00
-- url     : https://prove2.me/submissions/91354aca-83ed-4af9-989a-ef9c336117f4

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_Legendre
import Theorems.Thm_DeletedPrimes_count_eq_sum
import Theorems.Thm_DeletedPrimes_natFloor_eq_sub_fract
import Theorems.Thm_DeletedPrimes_tsum_muS_div_split

set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
variable {S : Set ℕ}
namespace DeletedPrimes
theorem _root_.solution (hS : ∀ p ∈ S, p.Prime) (hsum : Summable fun d : ℕ => (muS S d : ℝ) / d)
    {x : ℝ} (hx : 1 ≤ x) :
    err S x = -(∑ d ∈ Finset.Icc 1 ⌊x⌋₊, (muS S d : ℝ) * saw (x / d)) - mertensS S x / 2
      - x * ∑' d : ℕ, (if x < d then (muS S d : ℝ) / d else 0) := by
  have hx0 : 0 ≤ x := by linarith
  have hcount : (count S x : ℝ) = x * ∑ d ∈ Finset.Icc 1 ⌊x⌋₊, (muS S d : ℝ) / d
      - ∑ d ∈ Finset.Icc 1 ⌊x⌋₊, (muS S d : ℝ) * saw (x / d) - mertensS S x / 2 := by
    rw [count_eq_sum hS x, mertensS, Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [natFloor_eq_sub_fract (div_nonneg hx0 (Nat.cast_nonneg d))]
    unfold saw
    ring
  unfold err density
  rw [hcount, tsum_muS_div_split hsum x]
  ring
end DeletedPrimes
