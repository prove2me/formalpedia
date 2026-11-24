-- Prove2me | solution 1 for Formalism.WindowSums.zv_pow_nat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:09:29.924719+00:00
-- url     : https://prove2.me/submissions/d8fcb209-35a9-4c67-8c66-dbf2690557a5

import Definitions.Def_Formalism_WindowSums_Statement
import Definitions.Def_Formalism_WindowSums_AnnihilatorPolynomials_ZpowVal
import Theorems.Thm_Formalism_WindowSums_zv_prime
import Theorems.Thm_Formalism_WindowSums_zv_not_dvd_of_dvd_sub_one
import Theorems.Thm_Formalism_WindowSums_zv_pow_prime_pow
import Theorems.Thm_Formalism_WindowSums_zv_not_dvd_cast

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.WindowSums
open Finset
variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]
namespace Formalism.WindowSums
theorem _root_.solution (x : ℤ_[ℓ]) (hx : (ℓ : ℤ_[ℓ]) ∣ x - 1)
    (h2 : ℓ = 2 → (ℓ : ℤ_[ℓ]) ^ 2 ∣ x - 1) {n : ℕ} (hn : n ≠ 0) :
    emultiplicity (ℓ : ℤ_[ℓ]) (x ^ n - 1) =
      emultiplicity (ℓ : ℤ_[ℓ]) (x - 1) + padicValNat ℓ n := by
  obtain ⟨e, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn ℓ hℓ.out.ne_one
  have hm0 : m ≠ 0 := right_ne_zero_of_mul hn
  have hy1 : (ℓ : ℤ_[ℓ]) ∣ x ^ ℓ ^ e - 1 := hx.trans (sub_one_dvd_pow_sub_one x _)
  have h1 := emultiplicity_pow_sub_pow_of_prime zv_prime hy1
    (zv_not_dvd_of_dvd_sub_one (by simpa using hy1)) (zv_not_dvd_cast hm)
  rw [one_pow] at h1
  have hv : padicValNat ℓ (ℓ ^ e * m) = e := by
    rw [padicValNat.mul (pow_ne_zero _ hℓ.out.ne_zero) hm0, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hm, add_zero]
  rw [pow_mul, h1, zv_pow_prime_pow x hx h2 e, hv]
end Formalism.WindowSums
