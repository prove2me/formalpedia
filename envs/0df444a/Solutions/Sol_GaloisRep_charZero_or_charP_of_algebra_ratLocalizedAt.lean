-- Prove2me | solution 1 for GaloisRep.charZero_or_charP_of_algebra_ratLocalizedAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/e056b2ce-4e71-5e3b-bfa2-cf9760784613

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_GaloisRep_ratLocalizedAt_isUnit_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRep_charZero_or_charP_of_algebra_ratLocalizedAt

open GaloisRep

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

theorem solution (ℓ : ℕ) [Fact ℓ.Prime] (K : Type*) [Field K]
    [Algebra ↥(GaloisRep.ratLocalizedAt ℓ) K] :
    CharZero K ∨ CharP K ℓ := by
  have hℓ : ℓ.Prime := Fact.out
  obtain ⟨p, hp⟩ := CharP.exists K
  rcases CharP.char_is_prime_or_zero K p with hprime | h0
  · rcases eq_or_ne p ℓ with rfl | hpℓ
    · exact Or.inr hp
    · exfalso
      have hunit : IsUnit ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt ℓ)) := by
        rw [GaloisRep.ratLocalizedAt.isUnit_iff hℓ]
        have hcoe : (((p : ℕ) : ↥(GaloisRep.ratLocalizedAt ℓ)) : ℚ) = (p : ℚ) := by
          push_cast
          ring
        rw [hcoe, Rat.num_natCast, Int.natAbs_natCast]
        exact fun hdvd => hpℓ ((Nat.prime_dvd_prime_iff_eq hℓ hprime).mp hdvd).symm
      have hK : IsUnit ((p : ℕ) : K) := by
        have h := hunit.map (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) K)
        rwa [map_natCast] at h
      exact hK.ne_zero (CharP.cast_eq_zero K p)
  · subst h0
    exact Or.inl (CharP.charP_to_charZero K)

end
end S_GaloisRep_charZero_or_charP_of_algebra_ratLocalizedAt
end P2MW
export P2MW.S_GaloisRep_charZero_or_charP_of_algebra_ratLocalizedAt (solution)
