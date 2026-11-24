-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.v_natCast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:41:00.556378+00:00
-- url     : https://prove2.me/submissions/806ff7a4-f3e4-4225-a98d-5d360e722f16

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Theorems.Thm_Formalism_MainNotions_PlaneGram_v_natCast_of_not_dvd
import Theorems.Thm_Formalism_MainNotions_PlaneGram_v_p_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K] (v : AddValuation K (WithTop ℚ))
variable {v} {p : ℕ} [CharZero K]
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (hD : DVRHyp v p) {n : ℕ} (hn : n ≠ 0) :
    v (n : K) = ((padicValNat p n : ℚ) : WithTop ℚ) := by
  haveI := Fact.mk hD.prime
  obtain ⟨e, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hD.prime.ne_one
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero p)
  rw [padicValNat.mul (pow_ne_zero _ hD.prime.ne_zero) hm0, padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd hm, add_zero, Nat.cast_mul, Nat.cast_pow, v.map_mul,
    v_p_pow hD, v_natCast_of_not_dvd hD hm, add_zero]
end Formalism.MainNotions.PlaneGram
