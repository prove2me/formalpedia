-- Prove2me | solution 1 for Formalism.HC.Der.kc_pairing
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:10.486247+00:00
-- url     : https://prove2.me/submissions/98b35998-ab0b-4cc8-9f42-1f9505c6850f

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_KcPair
import Theorems.Thm_Formalism_HC_Der_kc_nf_map
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
private theorem prod_normalizedFactors_ideal_eq_self {S : Type*} [CommRing S] [IsDedekindDomain S]
    {I : Ideal S} (hI : I ≠ ⊥) : (normalizedFactors I).prod = I := by
  have hI0 : I ≠ 0 := by rw [Ideal.zero_eq_bot]; exact hI
  exact associated_iff_eq.mp (prod_normalizedFactors hI0)
private theorem mem_of_prime_dvd_multiset_prod {S : Type*} [CommRing S] [IsDedekindDomain S]
    {s : Multiset (Ideal S)} (hs : ∀ Q ∈ s, Prime Q) {P : Ideal S} (hP : Prime P)
    (h : P ∣ s.prod) : P ∈ s := by
  obtain ⟨Q, hQ, hPQ⟩ := hP.exists_mem_multiset_dvd h
  rwa [(prime_dvd_prime_iff_eq hP (hs Q hQ)).mp hPQ]
end
open NumberField Ideal
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
end Formalism.HC.Der
end

set_option autoImplicit false
open Formalism Formalism.HC Formalism.HC.Der
open Ideal UniqueFactorizationMonoid
namespace Formalism.HC.Der
theorem _root_.solution {S : Type*} [CommRing S] [IsDedekindDomain S] (D : Ideal S) (hD0 : D ≠ ⊥)
    (f : Ideal S ≃* Ideal S) (hfD : f D = D) (p : Ideal S → Prop)
    (hp : ∀ P ∈ normalizedFactors D, (p (f P) ↔ ¬ p P)) :
    ∃ B : Ideal S, D = B * f B ∧ (∀ P : Ideal S, P.IsPrime → P ∣ B → p P) ∧ B ⊔ f B = ⊤ ∧
      (∀ g : Ideal S ≃* Ideal S, g D = D → (∀ P ∈ normalizedFactors D, (p (g P) ↔ p P)) → g B = B) ∧
      ∀ B' : Ideal S, D = B' * f B' → (∀ P : Ideal S, P.IsPrime → P ∣ B' → p P) → B' = B := by
  classical
  obtain ⟨F, hFdef⟩ : ∃ F, F = normalizedFactors D := ⟨_, rfl⟩
  have hFp : ∀ Q ∈ F, Prime Q := fun Q hQ => prime_of_normalized_factor Q (hFdef ▸ hQ)
  have hpF : ∀ P ∈ F, (p (f P) ↔ ¬ p P) := fun P hP => hp P (hFdef ▸ hP)
  have hinv : ∀ g : Ideal S ≃* Ideal S, g D = D → F.map g = F := by
    intro g hg
    have := kc_nf_map D hD0 g
    rw [hg] at this
    rw [hFdef]
    exact this.symm
  have hFprod : F.prod = D := by rw [hFdef]; exact prod_normalizedFactors_ideal_eq_self hD0
  have hmap : (F.filter p).map f = F.filter (fun P => ¬ p P) := by
    have e1 : F.filter (fun P => ¬ p P) = (F.map f).filter (fun P => ¬ p P) := by
      rw [hinv f hfD]
    have e2 : (F.map f).filter (fun P => ¬ p P) = (F.filter (fun P => ¬ p (f P))).map f := by
      rw [Multiset.filter_map]
      rfl
    have e3 : F.filter (fun P => ¬ p (f P)) = F.filter p :=
      Multiset.filter_congr (fun P hP => by rw [hpF P hP]; exact not_not)
    rw [e1, e2, e3]
  have hsplit : D = (F.filter p).prod * f (F.filter p).prod := by
    rw [map_multiset_prod, hmap, Multiset.prod_filter_mul_prod_filter_not, hFprod]
  have hB0 : (F.filter p).prod ≠ ⊥ := by
    intro h
    apply hD0
    rw [hsplit, h, Ideal.bot_mul]
  have hprime_ne : ∀ {P J : Ideal S}, J ≠ ⊥ → P.IsPrime → P ∣ J → Prime P := by
    intro P J hJ hP hPJ
    refine Ideal.prime_of_isPrime ?_ hP
    rintro rfl
    exact hJ (zero_dvd_iff.mp hPJ)
  have hsupp : ∀ P : Ideal S, P.IsPrime → P ∣ (F.filter p).prod → p P := by
    intro P hP hdvd
    have hm := mem_of_prime_dvd_multiset_prod (fun Q hQ => hFp Q (Multiset.mem_of_mem_filter hQ))
      (hprime_ne hB0 hP hdvd) hdvd
    exact (Multiset.mem_filter.mp hm).2
  refine ⟨(F.filter p).prod, hsplit, hsupp, ?_, ?_, ?_⟩
  · by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    have hM1 : M ∣ (F.filter p).prod := Ideal.dvd_iff_le.mpr (le_sup_left.trans hle)
    have hM2 : M ∣ f (F.filter p).prod := Ideal.dvd_iff_le.mpr (le_sup_right.trans hle)
    have hpM := hsupp M hM.isPrime hM1
    rw [map_multiset_prod, hmap] at hM2
    have hm := mem_of_prime_dvd_multiset_prod (fun Q hQ => hFp Q (Multiset.mem_of_mem_filter hQ))
      (hprime_ne hB0 hM.isPrime hM1) hM2
    exact (Multiset.mem_filter.mp hm).2 hpM
  · intro g hgD hgp
    have e1 : (F.map g).filter p = (F.filter (fun P => p (g P))).map g := by
      rw [Multiset.filter_map]
      rfl
    have e2 : F.filter (fun P => p (g P)) = F.filter p :=
      Multiset.filter_congr (fun P hP => hgp P (hFdef ▸ hP))
    rw [map_multiset_prod, ← e2, ← e1, hinv g hgD, e2]
  · intro B' hB' hsupp'
    have hB'0 : B' ≠ ⊥ := by
      intro h; apply hD0; rw [hB', h, Ideal.bot_mul]
    have hfB'0 : f B' ≠ ⊥ := by
      intro h; apply hD0; rw [hB', h, Ideal.mul_bot]
    have hB'0' : B' ≠ 0 := by rw [Ideal.zero_eq_bot]; exact hB'0
    have hfB'0' : f B' ≠ 0 := by rw [Ideal.zero_eq_bot]; exact hfB'0
    have hF' : F = normalizedFactors B' + (normalizedFactors B').map f := by
      rw [hFdef, hB', normalizedFactors_mul hB'0' hfB'0', kc_nf_map B' hB'0 f]
    have hpB' : ∀ Q ∈ normalizedFactors B', p Q := by
      intro Q hQ
      exact hsupp' Q (Ideal.isPrime_of_prime (prime_of_normalized_factor Q hQ))
        (dvd_of_mem_normalizedFactors hQ)
    have hfilt : F.filter p = normalizedFactors B' := by
      rw [hF', Multiset.filter_add, Multiset.filter_eq_self.mpr hpB',
        Multiset.filter_eq_nil.mpr, add_zero]
      intro Q hQ
      obtain ⟨R, hR, rfl⟩ := Multiset.mem_map.mp hQ
      have hRF : R ∈ F := by rw [hF']; exact Multiset.mem_add.mpr (Or.inl hR)
      exact fun h => ((hpF R hRF).mp h) (hpB' R hR)
    rw [hfilt, prod_normalizedFactors_ideal_eq_self hB'0]
end Formalism.HC.Der
