-- Prove2me | solution 1 for DeletedPrimes.sum_range_muS_prime_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:58:14.648789+00:00
-- url     : https://prove2.me/submissions/5ab890fa-7736-4926-a798-60e519ebc142

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_Legendre
import Theorems.Thm_DeletedPrimes_muS_one
import Theorems.Thm_DeletedPrimes_muS_prime_pow

set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
variable {S : Set ℕ}
namespace DeletedPrimes
theorem _root_.solution {p : ℕ} (hp : p.Prime) :
    ∀ k : ℕ, ∑ j ∈ Finset.range (k + 2), muS S (p ^ j) = 1 + muS S p
  | 0 => by simp [Finset.sum_range_succ, muS_one]
  | k + 1 => by
    rw [Finset.sum_range_succ, solution hp k, muS_prime_pow hp (by omega), add_zero]
end DeletedPrimes
