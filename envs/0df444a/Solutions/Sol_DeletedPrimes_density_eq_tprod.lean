-- Prove2me | solution 1 for DeletedPrimes.density_eq_tprod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:14:36.926925+00:00
-- url     : https://prove2.me/submissions/e683b7f8-eedc-40a4-aa06-d6c6a441973c

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_Legendre
import Theorems.Thm_DeletedPrimes_muS_one
import Theorems.Thm_DeletedPrimes_muS_prime
import Theorems.Thm_DeletedPrimes_muS_prime_pow
import Theorems.Thm_DeletedPrimes_muS_mul_of_coprime
import Theorems.Thm_DeletedPrimes_summable_abs_muS_div

set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
variable {S : Set ℕ}
namespace DeletedPrimes
theorem _root_.solution
    (h1 : Summable (S.indicator fun n : ℕ => (n : ℝ) ^ (-1 : ℝ))) :
    density S = ∏' p : Nat.Primes, (if (p : ℕ) ∈ S then 1 - 1 / (p : ℝ) else 1) := by
  have hf₁ : (muS S 1 : ℝ) / ((1 : ℕ) : ℝ) = 1 := by simp [muS_one]
  have hmul : ∀ {m n : ℕ}, Nat.Coprime m n →
      (muS S (m * n) : ℝ) / ((m * n : ℕ) : ℝ) =
        (muS S m : ℝ) / (m : ℝ) * ((muS S n : ℝ) / (n : ℝ)) := by
    intro m n h
    rw [muS_mul_of_coprime h, Int.cast_mul, Nat.cast_mul, mul_div_mul_comm]
  have hsum : Summable fun n : ℕ => ‖(muS S n : ℝ) / (n : ℝ)‖ := summable_abs_muS_div h1
  have hf₀ : (muS S 0 : ℝ) / ((0 : ℕ) : ℝ) = 0 := by simp
  unfold density
  rw [← EulerProduct.eulerProduct_tprod (f := fun n : ℕ => (muS S n : ℝ) / (n : ℝ)) hf₁ hmul hsum
    hf₀]
  refine tprod_congr fun p => ?_
  have hp := p.prop
  rw [tsum_eq_sum (s := Finset.range 2)]
  · simp [Finset.sum_range_succ, muS_one, muS_prime hp]
    split_ifs <;> ring
  · intro e he
    simp only [Finset.mem_range, not_lt] at he
    simp [muS_prime_pow hp he]
end DeletedPrimes
