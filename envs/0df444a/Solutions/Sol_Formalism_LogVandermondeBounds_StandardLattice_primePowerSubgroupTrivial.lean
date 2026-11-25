-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.StandardLattice.primePowerSubgroupTrivial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:17:09.711047+00:00
-- url     : https://prove2.me/submissions/5f0a3a70-d1c6-49ea-b54e-967962f9defc

import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeVariationUnbounded
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_PrimePowerSubgroupTrivial
import Theorems.Thm_Formalism_LogVandermondeBounds_StandardLattice_primeOrderFinrank

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.StandardLattice
open Polynomial
namespace Formalism.LogVandermondeBounds.StandardLattice
theorem _root_.solution : PrimePowerSubgroupTrivial := by
  intro K _ _ n g Γ hg hfin hcard hlt
  obtain ⟨e, he⟩ := hcard
  rw [Subgroup.eq_bot_iff_forall]
  intro γ hγ
  by_contra hne
  set x : Γ := ⟨γ, hγ⟩ with hxdef
  have hx : x ≠ 1 := fun h => hne (congrArg Subtype.val h)
  have hdvd : orderOf x ∣ g ^ e := by
    rw [← he]
    exact orderOf_dvd_natCard x
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hg).1 hdvd
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hx (orderOf_eq_one_iff.1 (by simpa using hm))
  set y := x ^ (g ^ (m - 1)) with hy
  have hyg : y ^ g = 1 := by
    rw [hy, ← pow_mul, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hm0), ← hm,
      pow_orderOf_eq_one]
  have hy1 : y ≠ 1 := by
    intro h
    have h3 := orderOf_dvd_of_pow_eq_one (show x ^ (g ^ (m - 1)) = 1 from h)
    rw [hm] at h3
    have := (Nat.pow_dvd_pow_iff_le_right hg.one_lt).1 h3
    omega
  have key := primeOrderFinrank K n g ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) hg
    (by rw [← Units.val_pow_eq_pow_val, ← Subgroup.coe_pow, hyg]; rfl)
    (fun h => hy1 (Subtype.ext (Units.ext (by simpa using h))))
  omega
end Formalism.LogVandermondeBounds.StandardLattice
