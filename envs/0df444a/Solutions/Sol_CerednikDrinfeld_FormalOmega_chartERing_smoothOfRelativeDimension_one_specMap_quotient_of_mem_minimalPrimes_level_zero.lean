-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.chartERing.smoothOfRelativeDimension_one_specMap_quotient_of_mem_minimalPrimes_level_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/f3ea76f4-53a0-5ed9-84d0-e4a7a414d7b8

import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import Theorems.Thm_MvPolynomial_isStandardSmoothOfRelativeDimension_natCard
import Theorems.Thm_CerednikDrinfeld_FormalOmega_chartERing_eq_span_xi_or_eq_span_eta_of_mem_minimalPrimes_level_zero
import Theorems.Thm_CerednikDrinfeld_FormalOmega_chartERing_exists_ringEquiv_quotient_level_zero_span_ofPoly_X_localizationAway
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_chartERing_smoothOfRelativeDimension_one_specMap_quotient_of_mem_minimalPrimes_level_zero

set_option autoImplicit false

p2m_open "CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_chartERing_smoothOfRelativeDimension_one_specMap_quotient_of_mem_minimalPrimes_level_zero.CerednikDrinfeld CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_chartERing_smoothOfRelativeDimension_one_specMap_quotient_of_mem_minimalPrimes_level_zero.CerednikDrinfeld.FormalOmega AlgebraicGeometry CategoryTheory"

namespace CerednikDrinfeld p2m_export "CerednikDrinfeld" "FormalOmega.chartERing FormalOmega.chartERing.eq_span_xi_or_eq_span_eta_of_mem_minimalPrimes_level_zero FormalOmega.chartERing.exists_ringEquiv_quotient_level_zero_span_ofPoly_X_localizationAway" namespace FormalOmega p2m_export "CerednikDrinfeld.FormalOmega" "edgeQuot edgeDiscr edgeQuot.discr chartERing chartERing.eq_span_xi_or_eq_span_eta_of_mem_minimalPrimes_level_zero chartERing.exists_ringEquiv_quotient_level_zero_span_ofPoly_X_localizationAway" namespace chartERing p2m_export "CerednikDrinfeld.FormalOmega.chartERing" "ξ η eq_span_xi_or_eq_span_eta_of_mem_minimalPrimes_level_zero exists_ringEquiv_quotient_level_zero_span_ofPoly_X_localizationAway" end CerednikDrinfeld.FormalOmega.chartERing
p2m_open_scoped "CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.FormalOmega.chartERing" in

theorem CerednikDrinfeld.FormalOmega.chartERing.branchSmooth_aux29
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (r : ℕ) (J : Ideal ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)})))
    (e : (((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)})) ⧸ J) ≃+* Localization.Away ((MvPolynomial.X () : MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) ^ (r - 1) - 1))
    (he : ∀ a : 𝒪, e (Ideal.Quotient.mk _ (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (algebraMap 𝒪 (chartERing 𝒪 π r) a))) =
          algebraMap (𝒪 ⧸ Ideal.span {π ^ (0 + 1)}) _ (Ideal.Quotient.mk _ a)) :
    RingHom.IsStandardSmoothOfRelativeDimension (R := 𝒪 ⧸ Ideal.span {π ^ (0 + 1)}) (S := ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)})) ⧸ J) 1 ((Ideal.Quotient.mk J).comp
      (Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (algebraMap 𝒪 (chartERing 𝒪 π r))
        (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Ideal.mem_comap.mpr (by rw [map_pow]; exact Ideal.subset_span rfl)))))) := by
  classical
  set k := 𝒪 ⧸ Ideal.span {π ^ (0 + 1)} with hk
  set B := Localization.Away ((MvPolynomial.X () : MvPolynomial Unit k) ^ (r - 1) - 1) with hB
  set f := (Ideal.Quotient.mk J).comp
      (Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (algebraMap 𝒪 (chartERing 𝒪 π r))
        (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Ideal.mem_comap.mpr (by rw [map_pow]; exact Ideal.subset_span rfl))))) with hf
  letI algA : Algebra k (((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)})) ⧸ J) := RingHom.toAlgebra (R := k) (S := ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)})) ⧸ J) f

  haveI h1 : Algebra.IsStandardSmoothOfRelativeDimension 1 k (MvPolynomial Unit k) := by
    have := MvPolynomial.isStandardSmoothOfRelativeDimension_natCard k Unit
    rwa [Nat.card_unique] at this
  haveI h0 : Algebra.IsStandardSmoothOfRelativeDimension 0 (MvPolynomial Unit k) B :=
    Algebra.IsStandardSmoothOfRelativeDimension.localization_away ((MvPolynomial.X () : MvPolynomial Unit k) ^ (r - 1) - 1)
  have hB1 : Algebra.IsStandardSmoothOfRelativeDimension 1 k B :=
    Algebra.IsStandardSmoothOfRelativeDimension.trans 1 0 k (MvPolynomial Unit k) B

  let e' : (((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)})) ⧸ J) ≃ₐ[k] B := AlgEquiv.ofRingEquiv (f := e) (fun x => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [← he a]
    rfl)
  haveI := hB1
  have hA : Algebra.IsStandardSmoothOfRelativeDimension 1 k (((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)})) ⧸ J) :=
    Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv 1 e'.symm
  unfold RingHom.IsStandardSmoothOfRelativeDimension
  exact hA

theorem solution
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (r : ℕ) (hπ : (Ideal.span ({π} : Set 𝒪)).IsMaximal)
    (P : Ideal ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)})))
    (hP : P ∈ minimalPrimes ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}))) :
    SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom (R := 𝒪 ⧸ Ideal.span {π ^ (0 + 1)})
      (S := ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)})) ⧸ P) ((Ideal.Quotient.mk P).comp
      (Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (algebraMap 𝒪 (chartERing 𝒪 π r))
        (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Ideal.mem_comap.mpr (by rw [map_pow]; exact Ideal.subset_span rfl)))))))) := by
  classical

  refine (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)).mpr ?_
  rw [CommRingCat.hom_ofHom]
  apply RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso

  rcases lt_or_ge 1 r with hr | hr
  swap
  · exfalso
    have hr0 : r - 1 = 0 := by omega
    have h0 : edgeQuot.discr 𝒪 π r = 0 := by
      simp [edgeQuot.discr, edgeDiscr, hr0]
    haveI : Unique (chartERing 𝒪 π r) :=
      IsLocalization.uniqueOfZeroMem (M := Submonoid.powers (edgeQuot.discr 𝒪 π r)) (h0 ▸ Submonoid.mem_powers _)
    haveI : Subsingleton ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)})) := Function.Surjective.subsingleton Ideal.Quotient.mk_surjective
    exact hP.1.1.ne_top ((Ideal.eq_top_iff_one _).mpr (by rw [Subsingleton.elim (1 : ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}))) 0]; exact P.zero_mem))

  rcases CerednikDrinfeld.FormalOmega.chartERing.eq_span_xi_or_eq_span_eta_of_mem_minimalPrimes_level_zero 𝒪 π r hπ P hP with hPe | hPe
  · subst hPe
    obtain ⟨e, he, -⟩ :=
      CerednikDrinfeld.FormalOmega.chartERing.exists_ringEquiv_quotient_level_zero_span_ofPoly_X_localizationAway 𝒪 π r hπ hr 0
    exact CerednikDrinfeld.FormalOmega.chartERing.branchSmooth_aux29 𝒪 π r _ e he
  · subst hPe
    obtain ⟨e, he, -⟩ :=
      CerednikDrinfeld.FormalOmega.chartERing.exists_ringEquiv_quotient_level_zero_span_ofPoly_X_localizationAway 𝒪 π r hπ hr 1
    exact CerednikDrinfeld.FormalOmega.chartERing.branchSmooth_aux29 𝒪 π r _ e he

end S_CerednikDrinfeld_FormalOmega_chartERing_smoothOfRelativeDimension_one_specMap_quotient_of_mem_minimalPrimes_level_zero
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_chartERing_smoothOfRelativeDimension_one_specMap_quotient_of_mem_minimalPrimes_level_zero (solution)
