-- Prove2me | solution 1 for DeletedPrimes.summable_muS_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:06:24.484801+00:00
-- url     : https://prove2.me/submissions/e157758a-99e2-4523-80e4-cfa16dd5b7ea

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_Legendre
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
    Summable fun d : ℕ => (muS S d : ℝ) / d :=
  Summable.of_norm (summable_abs_muS_div h1)
end DeletedPrimes
