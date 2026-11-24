-- Prove2me | solution 1 for DeletedPrimes.muS_mul_of_coprime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:58:53.779802+00:00
-- url     : https://prove2.me/submissions/c539ee99-9cf4-4689-b011-5203123a38e2

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_Legendre
import Theorems.Thm_DeletedPrimes_muS_mul_of_coprime_aux

set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
variable {S : Set ℕ}
namespace DeletedPrimes
theorem _root_.solution {q d : ℕ} (h : Nat.Coprime q d) : muS S (q * d) = muS S q * muS S d :=
  muS_mul_of_coprime_aux h
end DeletedPrimes
