-- Prove2me | solution 1 for Formalism.WindowSums.zv_pow_prime_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:55:29.32568+00:00
-- url     : https://prove2.me/submissions/ee2029b9-f0db-487c-a6fa-ae147340cbe8

import Definitions.Def_Formalism_WindowSums_Statement
import Definitions.Def_Formalism_WindowSums_AnnihilatorPolynomials_ZpowVal
import Theorems.Thm_Formalism_WindowSums_zv_prime
import Theorems.Thm_Formalism_WindowSums_zv_not_dvd_of_dvd_sub_one
import Theorems.Thm_Formalism_WindowSums_zv_two_sq_step

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
    (h2 : ℓ = 2 → (ℓ : ℤ_[ℓ]) ^ 2 ∣ x - 1) (k : ℕ) :
    emultiplicity (ℓ : ℤ_[ℓ]) (x ^ ℓ ^ k - 1) = emultiplicity (ℓ : ℤ_[ℓ]) (x - 1) + k := by
  by_cases hl : ℓ = 2
  · have h4 := h2 hl
    induction k with
    | zero => simp
    | succ k ih =>
      have hy : (ℓ : ℤ_[ℓ]) ^ 2 ∣ x ^ ℓ ^ k - 1 := h4.trans (sub_one_dvd_pow_sub_one x _)
      have e : x ^ ℓ ^ (k + 1) = (x ^ ℓ ^ k) ^ 2 := by
        rw [pow_succ, pow_mul]
        exact congrArg (fun n => (x ^ ℓ ^ k) ^ n) hl
      rw [e, zv_two_sq_step hl hy, ih]
      push_cast
      ring
  · have hodd : Odd ℓ := hℓ.out.odd_of_ne_two hl
    have h1 := emultiplicity_pow_prime_pow_sub_pow_prime_pow (x := x) (y := 1) zv_prime hodd
      (by simpa using hx) (zv_not_dvd_of_dvd_sub_one hx) k
    rwa [one_pow] at h1
end Formalism.WindowSums
