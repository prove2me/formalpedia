-- Prove2me | solution 1 for DeletedPrimes.muSFun_mul_zeta
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:01:08.758629+00:00
-- url     : https://prove2.me/submissions/8b34c6ca-1e48-4410-8db7-bdb1fce973bf

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_Legendre
import Theorems.Thm_DeletedPrimes_muS_one
import Theorems.Thm_DeletedPrimes_muS_prime
import Theorems.Thm_DeletedPrimes_muSFun_apply
import Theorems.Thm_DeletedPrimes_isMultiplicative_muSFun
import Theorems.Thm_DeletedPrimes_sfreeFun_apply
import Theorems.Thm_DeletedPrimes_isMultiplicative_sfreeFun
import Theorems.Thm_DeletedPrimes_sum_range_muS_prime_pow

set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
variable {S : Set ℕ}
namespace DeletedPrimes
theorem _root_.solution (hS : ∀ p ∈ S, p.Prime) :
    muSFun S * (ArithmeticFunction.zeta : ArithmeticFunction ℤ) = sfreeFun S := by
  rw [ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _
    (isMultiplicative_muSFun.mul ArithmeticFunction.isMultiplicative_zeta.natCast) _
    (isMultiplicative_sfreeFun hS)]
  intro p i hp
  rw [ArithmeticFunction.coe_mul_zeta_apply, Nat.sum_divisors_prime_pow hp, sfreeFun_apply]
  simp only [muSFun_apply]
  rcases i with _ | k
  · simp [muS_one]
    exact fun q hq hdvd => (hS q hq).one_lt.ne' (Nat.dvd_one.mp hdvd)
  · rw [sum_range_muS_prime_pow hp k, muS_prime hp]
    have hne : p ^ (k + 1) ≠ 0 := pow_ne_zero _ hp.ne_zero
    by_cases hpS : p ∈ S
    · rw [if_pos hpS, if_neg]
      · norm_num
      · rintro ⟨_, h⟩
        exact h p hpS (dvd_pow_self p (Nat.succ_ne_zero k))
    · rw [if_neg hpS, if_pos]
      · norm_num
      · refine ⟨hne, fun q hq hdvd => ?_⟩
        have := (Nat.prime_dvd_prime_iff_eq (hS q hq) hp).mp ((hS q hq).dvd_of_dvd_pow hdvd)
        exact hpS (this ▸ hq)
end DeletedPrimes
