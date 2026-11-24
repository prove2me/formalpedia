-- Prove2me | solution 1 for Formalism.HC.Der.kc_nf_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:21.153125+00:00
-- url     : https://prove2.me/submissions/f2139c5c-1045-4536-8019-a802b9902a32

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_KcPair
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.HC.Der
section
open Ideal UniqueFactorizationMonoid
private theorem mulEquiv_ideal_bot_eq_bot {S : Type*} [CommRing S] [IsDedekindDomain S]
    (f : Ideal S ≃* Ideal S) : f ⊥ = ⊥ := by
  obtain ⟨J, hJ⟩ := f.surjective ⊥
  calc f ⊥ = f (⊥ * J) := by rw [Ideal.bot_mul]
    _ = f ⊥ * f J := map_mul f _ _
    _ = ⊥ := by rw [hJ, Ideal.mul_bot]
private theorem prime_mulEquiv_ideal_apply {S : Type*} [CommRing S] [IsDedekindDomain S]
    (f : Ideal S ≃* Ideal S) {P : Ideal S} (hP : Prime P) : Prime (f P) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    apply hP.ne_zero
    apply f.injective
    rw [Ideal.zero_eq_bot] at h ⊢
    rw [h, mulEquiv_ideal_bot_eq_bot f]
  · intro hu
    apply hP.not_unit
    rw [isUnit_iff_eq_one] at hu ⊢
    apply f.injective
    rw [hu, map_one]
  · intro a b h
    have h' : P ∣ f.symm a * f.symm b := by
      have := map_dvd f.symm h
      rwa [map_mul, MulEquiv.symm_apply_apply] at this
    rcases hP.dvd_or_dvd h' with h1 | h1
    · left
      have := map_dvd f h1
      rwa [MulEquiv.apply_symm_apply] at this
    · right
      have := map_dvd f h1
      rwa [MulEquiv.apply_symm_apply] at this
private theorem prod_normalizedFactors_ideal_eq_self {S : Type*} [CommRing S] [IsDedekindDomain S]
    {I : Ideal S} (hI : I ≠ ⊥) : (normalizedFactors I).prod = I := by
  have hI0 : I ≠ 0 := by rw [Ideal.zero_eq_bot]; exact hI
  exact associated_iff_eq.mp (prod_normalizedFactors hI0)
end
open NumberField Ideal
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
end Formalism.HC.Der
end

set_option autoImplicit false
open Formalism Formalism.HC Formalism.HC.Der
open Ideal UniqueFactorizationMonoid
namespace Formalism.HC.Der
theorem _root_.solution {S : Type*} [CommRing S] [IsDedekindDomain S] (I : Ideal S) (hI : I ≠ ⊥)
    (f : Ideal S ≃* Ideal S) : normalizedFactors (f I) = (normalizedFactors I).map f := by
  calc normalizedFactors (f I) = normalizedFactors ((normalizedFactors I).map f).prod := by
        rw [← map_multiset_prod f, prod_normalizedFactors_ideal_eq_self hI]
    _ = (normalizedFactors I).map f := by
        apply normalizedFactors_prod_of_prime
        intro Q hQ
        obtain ⟨R, hR, rfl⟩ := Multiset.mem_map.mp hQ
        exact prime_mulEquiv_ideal_apply f (prime_of_normalized_factor R hR)
end Formalism.HC.Der
