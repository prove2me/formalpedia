-- Prove2me | solution 1 for DeletedPrimes.sum_divisors_muS
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:14:10.696795+00:00
-- url     : https://prove2.me/submissions/b348de75-e02d-49f1-bcde-9a84fd5e72ce

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_Legendre
import Theorems.Thm_DeletedPrimes_muSFun_apply
import Theorems.Thm_DeletedPrimes_sfreeFun_apply
import Theorems.Thm_DeletedPrimes_muSFun_mul_zeta

set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
variable {S : Set ℕ}
namespace DeletedPrimes
theorem _root_.solution (hS : ∀ p ∈ S, p.Prime) {n : ℕ} (hn : 0 < n) :
    ∑ d ∈ n.divisors, muS S d = if SFree S n then 1 else 0 := by
  have := congrArg (fun f => f n) (muSFun_mul_zeta hS)
  simp only [ArithmeticFunction.coe_mul_zeta_apply, muSFun_apply, sfreeFun_apply] at this
  rw [this]
  simp [hn.ne']
end DeletedPrimes
