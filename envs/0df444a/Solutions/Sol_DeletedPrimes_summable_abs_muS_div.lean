-- Prove2me | solution 1 for DeletedPrimes.summable_abs_muS_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:04:20.334902+00:00
-- url     : https://prove2.me/submissions/ea03cb4f-97bc-4272-80cb-3a361842cc5b

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_Legendre
import Theorems.Thm_DeletedPrimes_summable_units_of_summable

set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
variable {S : Set ℕ}
namespace DeletedPrimes
theorem _root_.solution
    (h1 : Summable (S.indicator fun n : ℕ => (n : ℝ) ^ (-1 : ℝ))) :
    Summable fun d : ℕ => |(muS S d : ℝ) / d| := by
  have := summable_units_of_summable h1
  refine this.congr fun d => ?_
  rw [Real.rpow_neg_one, abs_div, Nat.abs_cast, div_eq_mul_inv]
end DeletedPrimes
