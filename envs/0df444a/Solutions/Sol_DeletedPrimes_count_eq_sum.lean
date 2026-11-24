-- Prove2me | solution 1 for DeletedPrimes.count_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:03:34.504236+00:00
-- url     : https://prove2.me/submissions/33800fc2-3d4b-4633-b92f-b9c9a2e63501

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_Legendre
import Theorems.Thm_DeletedPrimes_muSFun_apply
import Theorems.Thm_DeletedPrimes_sfreeFun_apply
import Theorems.Thm_DeletedPrimes_muSFun_mul_zeta

set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
variable {S : Set ℕ}
namespace DeletedPrimes
theorem _root_.solution (hS : ∀ p ∈ S, p.Prime) (x : ℝ) :
    (count S x : ℝ) = ∑ d ∈ Finset.Icc 1 ⌊x⌋₊, (muS S d : ℝ) * (⌊x / d⌋₊ : ℝ) := by
  have key := ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum (muSFun S) ⌊x⌋₊
  rw [muSFun_mul_zeta hS] at key
  have hIcc : Finset.Icc 1 ⌊x⌋₊ = Finset.Ioc 0 ⌊x⌋₊ := rfl
  simp only [Nat.floor_div_natCast]
  unfold count
  rw [Finset.card_filter, hIcc]
  have key' := congrArg (fun z : ℤ => (z : ℝ)) key
  simp only [sfreeFun_apply, muSFun_apply, Int.cast_sum, Int.cast_mul, Int.cast_natCast] at key'
  push_cast
  rw [← key']
  refine Finset.sum_congr rfl fun n hn => ?_
  have : n ≠ 0 := by simp at hn; omega
  simp [this]
end DeletedPrimes
