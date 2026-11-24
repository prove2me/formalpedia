-- Prove2me | solution 1 for DeletedPrimes.isMultiplicative_muSFun
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:58:06.633956+00:00
-- url     : https://prove2.me/submissions/370f834f-47c2-4e47-9ca2-3a5a026a32c3

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_Legendre
import Theorems.Thm_DeletedPrimes_muS_one
import Theorems.Thm_DeletedPrimes_muS_mul_of_coprime_aux

set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
variable {S : Set ℕ}
namespace DeletedPrimes
theorem _root_.solution : (muSFun S).IsMultiplicative :=
  ⟨muS_one S, fun h => muS_mul_of_coprime_aux h⟩
end DeletedPrimes
