-- Prove2me | solution 1 for DeletedPrimes.dim_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:53:28.855025+00:00
-- url     : https://prove2.me/submissions/c0009622-e63f-4954-90aa-88b0945f1ee0

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_Legendre
import Theorems.Thm_DeletedPrimes_dim_set_two_mem

set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
variable {S : Set ℕ}
namespace DeletedPrimes
theorem _root_.solution (S : Set ℕ) : 0 ≤ dim S :=
  le_csInf ⟨2, dim_set_two_mem S⟩ fun _ h => h.1
end DeletedPrimes
