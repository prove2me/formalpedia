-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.hostOrbits
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:35:48.455804+00:00
-- url     : https://prove2.me/submissions/d407a8e5-adbb-4204-8cb3-1568bde7db8c

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostOrbitsPlaces
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Orbits
import Theorems.Thm_Formalism_FrobeniusOrbits_Orbits_orderOf_conjugation_eq_two

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Orbits
namespace Formalism.FrobeniusOrbits
theorem _root_.solution : HostOrbits := by
  unfold HostOrbits
  intro e φ hφ
  have hb : φ.1.2 = -1 := by rcases hφ with h | h <;> simp [h, c0]
  refine ⟨fun τ hτ i => ?_, fun h0 hne => ?_⟩
  · have hτ2 : τ.1.2 = 1 := by simpa [Psi, chD] using hτ
    have hm : (φ ^ i * τ).1.2 = (-1) ^ i := by simp [hb, hτ2]
    have : φ ^ i * τ ∈ Psi e ↔ (φ ^ i * τ).1.2 = 1 := by simp [Psi, chD]
    rw [this, hm]
    exact neg_one_pow_eq_one_iff_even (by decide)
  ·
    have hpow : ∀ x : HGrp e, x ^ (2 ^ (e + 1)) = 1 := by
      intro x
      obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
      have hc : Fintype.card (ZMod (2 ^ (e + 2)))ˣ = 2 ^ (e + 1) := by
        rw [ZMod.card_units_eq_totient, Nat.totient_prime_pow_succ Nat.prime_two]
        simp
      rw [← QuotientGroup.mk_pow, ← hc, pow_card_eq_one, QuotientGroup.mk_one]
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one (hpow φ.2))
    have hj0 : j ≠ 0 := by
      rintro rfl
      exact hne (orderOf_eq_one_iff.mp (by simpa using hj))
    have hev : Even (orderOf φ.2) := by
      rw [hj]
      exact (Nat.even_pow.mpr ⟨even_two, hj0⟩)
    refine ⟨hev, ?_⟩
    rw [Prod.orderOf, h0, orderOf_conjugation_eq_two]
    exact Nat.lcm_eq_right (even_iff_two_dvd.mp hev)
end Formalism.FrobeniusOrbits
