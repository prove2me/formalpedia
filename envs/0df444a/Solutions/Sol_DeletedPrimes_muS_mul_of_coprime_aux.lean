-- Prove2me | solution 1 for DeletedPrimes.muS_mul_of_coprime_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:50:36.679941+00:00
-- url     : https://prove2.me/submissions/3b20a354-3da9-4dea-9985-720fb7bee44f

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_Legendre

set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
variable {S : Set ℕ}
namespace DeletedPrimes
theorem _root_.solution {q d : ℕ} (h : Nat.Coprime q d) :
    muS S (q * d) = muS S q * muS S d := by
  unfold muS
  rw [Nat.Coprime.primeFactors_mul h, ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime h]
  by_cases hq : ∀ p ∈ q.primeFactors, p ∈ S <;> by_cases hd : ∀ p ∈ d.primeFactors, p ∈ S
  · rw [if_pos (fun p hp => (Finset.mem_union.mp hp).elim (hq p) (hd p)), if_pos hq,
      if_pos hd]
  · rw [if_neg (fun h' => hd fun p hp => h' p (Finset.mem_union_right _ hp)), if_neg hd,
      mul_zero]
  · rw [if_neg (fun h' => hq fun p hp => h' p (Finset.mem_union_left _ hp)), if_neg hq,
      zero_mul]
  · rw [if_neg (fun h' => hq fun p hp => h' p (Finset.mem_union_left _ hp)), if_neg hq,
      zero_mul]
end DeletedPrimes
