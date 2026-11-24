-- Prove2me | solution 1 for Formalism.HC.Der.discr_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:12:54.049782+00:00
-- url     : https://prove2.me/submissions/7c219603-a510-46f8-90e7-7f2523085932

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_KcDiffSmulMem
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_KcPair
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_KcDiff
import Theorems.Thm_Formalism_HC_Der_kc_not_dvd_different
import Theorems.Thm_Formalism_HC_Der_kc_unr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise nonZeroDivisors
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
variable {φ : Frame} (H : HostRaw φ)
variable (C : HostCore H)
include C
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
namespace Formalism.HC.Der
theorem _root_.solution : discr H.E = discr H.F ^ 2 := by
  have := C.cm
  have hdiff : differentIdeal (𝓞 H.F) (𝓞 H.E) = ⊤ := by
    by_contra hne
    obtain ⟨P, hPmax, hle⟩ := Ideal.exists_le_maximal _ hne
    refine kc_not_dvd_different H.F H.E P ?_ (Ideal.dvd_iff_le.mpr hle)
    intro hbot σ hσ
    have hmem : σ ∈ Subgroup.zpowers (IsCMField.complexConj H.E) := by
      rw [IsCMField.zpowers_complexConj_eq_top]
      exact Subgroup.mem_top σ
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have h2 : k % (orderOf (IsCMField.complexConj H.E) : ℤ) = k % 2 := by
      rw [IsCMField.orderOf_complexConj]
      rfl
    rw [← zpow_mod_orderOf, h2] at hσ ⊢
    rcases Int.emod_two_eq_zero_or_one k with hk | hk
    · rw [hk, zpow_zero]
    · exfalso
      rw [hk, zpow_one] at hσ
      exact kc_unr H C P hPmax.isPrime hbot hσ
  have h := natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow H.F (𝓞 H.F) H.E (𝓞 H.E)
  rw [hdiff, Ideal.absNorm_top, one_mul, Algebra.IsQuadraticExtension.finrank_eq_two] at h
  have hsign : (discr H.E).sign = 1 := by
    rw [sign_discr]
    have h1 := IsTotallyComplex.finrank H.E
    rw [C.finrank_E] at h1
    have h3 : NumberField.InfinitePlace.nrComplexPlaces H.E = 2 * φ.ord := by omega
    rw [h3, pow_mul, neg_one_sq, one_pow]
  rw [← Int.sign_mul_natAbs (discr H.E), hsign, one_mul, h, Nat.cast_pow, Int.natAbs_sq]
end Formalism.HC.Der
