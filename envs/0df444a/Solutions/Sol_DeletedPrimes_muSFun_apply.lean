-- Prove2me | solution 1 for DeletedPrimes.muSFun_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:47:47.113703+00:00
-- url     : https://prove2.me/submissions/0130241b-42eb-4191-b5ae-cd46402ba34a

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_Legendre

set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
variable {S : Set ℕ}
namespace DeletedPrimes
theorem _root_.solution (n : ℕ) : muSFun S n = muS S n := rfl
end DeletedPrimes
