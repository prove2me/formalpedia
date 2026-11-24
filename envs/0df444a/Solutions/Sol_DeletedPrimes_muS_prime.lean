-- Prove2me | solution 1 for DeletedPrimes.muS_prime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:50:25.157358+00:00
-- url     : https://prove2.me/submissions/b5ff7f6f-5e13-4e39-91f7-9e424741fbbe

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_Legendre

set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
variable {S : Set ℕ}
namespace DeletedPrimes
theorem _root_.solution {p : ℕ} (hp : p.Prime) : muS S p = if p ∈ S then -1 else 0 := by
  simp [muS, hp.primeFactors, ArithmeticFunction.moebius_apply_prime hp]
end DeletedPrimes
