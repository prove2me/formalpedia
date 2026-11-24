-- Prove2me | solution 1 for Formalism.WindowSums.zv_two_sq_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:42:14.532802+00:00
-- url     : https://prove2.me/submissions/0719b896-6862-4bc4-9750-497ae043aa35

import Definitions.Def_Formalism_WindowSums_Statement
import Definitions.Def_Formalism_WindowSums_AnnihilatorPolynomials_ZpowVal
import Theorems.Thm_Formalism_WindowSums_zv_prime

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
theorem _root_.solution (h2 : ℓ = 2) {x : ℤ_[ℓ]} (h4 : (ℓ : ℤ_[ℓ]) ^ 2 ∣ x - 1) :
    emultiplicity (ℓ : ℤ_[ℓ]) (x ^ 2 - 1) = emultiplicity (ℓ : ℤ_[ℓ]) (x - 1) + 1 := by
  have hx1 : (ℓ : ℤ_[ℓ]) ∣ x - 1 := (dvd_pow_self _ two_ne_zero).trans h4
  have e : x + 1 = (x - 1) + (ℓ : ℤ_[ℓ]) := by
    have hc : (ℓ : ℤ_[ℓ]) = 2 := by
      have h7 := congrArg (fun n : ℕ => (n : ℤ_[ℓ])) h2
      simpa using h7
    rw [hc]
    ring

  have hp1 : emultiplicity (ℓ : ℤ_[ℓ]) (x + 1) = 1 := by
    rw [← Nat.cast_one (R := ℕ∞), emultiplicity_eq_coe]
    refine ⟨by rw [pow_one, e]; exact dvd_add hx1 dvd_rfl, fun hd => ?_⟩
    have h3 : (ℓ : ℤ_[ℓ]) ^ 2 ∣ (ℓ : ℤ_[ℓ]) ^ 1 := by
      have h5 := dvd_sub hd h4
      rw [e, add_sub_cancel_left] at h5
      rw [pow_one]
      exact h5
    have h6 := (pow_dvd_pow_iff zv_prime.ne_zero zv_prime.not_unit).1 h3
    omega
  rw [show x ^ 2 - 1 = (x - 1) * (x + 1) by ring, emultiplicity_mul zv_prime, hp1]
end Formalism.WindowSums
