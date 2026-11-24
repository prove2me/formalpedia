-- Prove2me | solution 1 for DeletedPrimes.dim_set_two_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:51:31.638638+00:00
-- url     : https://prove2.me/submissions/1559e9ba-045f-45aa-9358-f779671ce4ef

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_Legendre

set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
variable {S : Set ℕ}
namespace DeletedPrimes
theorem _root_.solution (S : Set ℕ) :
    (2 : ℝ) ∈ {σ : ℝ | 0 ≤ σ ∧ Summable (S.indicator fun n : ℕ => (n : ℝ) ^ (-σ))} :=
  ⟨by norm_num, (Real.summable_nat_rpow.mpr (by norm_num)).indicator S⟩
end DeletedPrimes
