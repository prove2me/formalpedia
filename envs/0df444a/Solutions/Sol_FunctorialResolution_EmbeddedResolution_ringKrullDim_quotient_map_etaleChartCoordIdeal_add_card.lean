-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.ringKrullDim_quotient_map_etaleChartCoordIdeal_add_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:31:59.369254+00:00
-- url     : https://prove2.me/submissions/818f899f-e992-44de-9a0c-e6bb1db39b7a

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinatePolynomialRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateSubscheme
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_DerivationLocalization
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_RegularLocalRing
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateQuotient
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_etaleChartCoordIdeal_eq_span_image
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isRegularLocalRing_quotient_map_etaleChartCoordIdeal
import Theorems.Thm_Derivation_liftToLocalization_algebraMap
import Theorems.Thm_Derivation_mapToLocalization_algebraMap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_coordRingHom_X
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_ofCoords_map
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_basisDerivation_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheaf_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isRegularLocalRing_of_isLocalization_etale
import Theorems.Thm_IsRegularLocalRing_ringKrullDim_quotient_span_singleton_add_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Derivation.liftToLocalization_algebraMap
attribute [local simp] Derivation.mapToLocalization_algebraMap
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleChart.coordRingHom_X
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleChart.ofCoords_map
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleCoordinates.basisDerivation_apply
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_ideal
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_zero
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheaf_ideal


section
universe u
namespace FunctorialResolution.EmbeddedResolution
private theorem algebraMap_etaleChartCoord_notMem_maximalIdeal_sq_sup (k : Type u) [Field k] (m : ℕ) (S : Type u) [CommRing S]
    [Algebra (CoordPolynomialRing k m) S] [Algebra.Etale (CoordPolynomialRing k m) S]
    (q : Ideal S) [q.IsPrime] (A : Type u) [CommRing A] [Algebra S A]
    [IsLocalization q.primeCompl A] [IsLocalRing A] (J' : Finset (Fin m))
    (hJ' : ∀ i ∈ J', etaleChartCoord k m S i ∈ q) (j : Fin m) (hj : j ∉ J') :
    algebraMap S A (etaleChartCoord k m S j) ∉
      IsLocalRing.maximalIdeal A ^ 2 ⊔ Ideal.map (algebraMap S A) (etaleChartCoordIdeal k m S J') := by
  classical
  let algebraKS : Algebra k S := ((algebraMap (CoordPolynomialRing k m) S).comp
    (algebraMap k (CoordPolynomialRing k m))).toAlgebra
  have : IsScalarTower k (CoordPolynomialRing k m) S := IsScalarTower.of_algebraMap_eq' rfl
  let algebraKA : Algebra k A := ((algebraMap S A).comp (algebraMap k S)).toAlgebra
  have : IsScalarTower k S A := IsScalarTower.of_algebraMap_eq' rfl
  let D : Derivation k S S :=
    EtaleCoordinates.partialDeriv k (ULift.{u} (Fin m)) S (ULift.up.{u} j)
  let DA : Derivation k A A := D.mapToLocalization q.primeCompl
  have hderivAlgebraMap : ∀ s : S, DA (algebraMap S A s) = algebraMap S A (D s) :=
    Derivation.mapToLocalization_algebraMap D q.primeCompl
  have hDx : D (etaleChartCoord k m S j) = 1 :=
    EtaleCoordinates.partialDeriv_coord_self k (ULift.{u} (Fin m)) S (ULift.up.{u} j)
  have hDne : ∀ i : Fin m, i ≠ j → D (etaleChartCoord k m S i) = 0 := by
    intro i hne
    have hup : (ULift.up.{u} j) ≠ ULift.up.{u} i := fun h => hne (congrArg ULift.down h).symm
    exact EtaleCoordinates.partialDeriv_coord_of_ne k (ULift.{u} (Fin m)) S
      (ULift.up.{u} j) (ULift.up.{u} i) hup
  have hmapeq : Ideal.map (algebraMap S A) (etaleChartCoordIdeal k m S J')
      = Ideal.span ((fun i : Fin m => algebraMap S A (etaleChartCoord k m S i)) ''
        (J' : Set (Fin m))) := by
    rw [etaleChartCoordIdeal_eq_span_image, Ideal.map_span, Set.image_image]
  have hspan_le : Ideal.span ((fun i : Fin m => algebraMap S A (etaleChartCoord k m S i)) ''
      (J' : Set (Fin m))) ≤ IsLocalRing.maximalIdeal A := by
    refine Ideal.span_le.mpr ?_
    rintro x ⟨i, hi, rfl⟩
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff A q (etaleChartCoord k m S i)
      inferInstance).mpr (hJ' i (Finset.mem_coe.mp hi))
  intro hmem
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hmem
  have hsq : IsLocalRing.maximalIdeal A ^ 2
      = IsLocalRing.maximalIdeal A * IsLocalRing.maximalIdeal A := sq _
  rw [hsq] at ha
  have hDa : DA a ∈ IsLocalRing.maximalIdeal A := by
    refine Submodule.mul_induction_on ha ?_ ?_
    · intro p hp r hr
      rw [DA.leibniz, smul_eq_mul, smul_eq_mul]
      exact add_mem (Ideal.mul_mem_right _ _ hp) (Ideal.mul_mem_right _ _ hr)
    · intro x y hx hy
      rw [map_add]
      exact add_mem hx hy
  rw [hmapeq] at hb
  have hDb : DA b ∈ IsLocalRing.maximalIdeal A := by
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hb
    · rintro z ⟨i, hi, rfl⟩
      rw [hderivAlgebraMap, hDne i (by rintro rfl; exact hj (Finset.mem_coe.mp hi)), map_zero]
      exact zero_mem _
    · rw [map_zero]
      exact zero_mem _
    · intro x y hx hy px py
      rw [map_add]
      exact add_mem px py
    · intro c x hx px
      have hxm : x ∈ IsLocalRing.maximalIdeal A := hspan_le hx
      rw [smul_eq_mul, DA.leibniz, smul_eq_mul, smul_eq_mul]
      exact add_mem (Ideal.mul_mem_left _ _ px) (Ideal.mul_mem_right _ _ hxm)
  have hone : DA (algebraMap S A (etaleChartCoord k m S j)) = 1 := by
    rw [hderivAlgebraMap, hDx, map_one]
  rw [← hab, map_add] at hone
  have h1 : (1 : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [← hone]
    exact add_mem hDa hDb
  exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
universe u
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (k : Type u) [Field k] (m : ℕ)
    (S : Type u) [CommRing S] [Algebra (CoordPolynomialRing k m) S]
    [Algebra.Etale (CoordPolynomialRing k m) S] (q : Ideal S) [q.IsPrime] (A : Type u) [CommRing A]
    [Algebra S A] [IsLocalization q.primeCompl A] (J : Finset (Fin m))
    (hJ : ∀ j ∈ J, etaleChartCoord k m S j ∈ q) :
    ringKrullDim (A ⧸ Ideal.map (algebraMap S A) (etaleChartCoordIdeal k m S J)) +
        (J.card : WithBot ℕ∞) = ringKrullDim A := by
  classical
  have : IsRegularLocalRing A := isRegularLocalRing_of_isLocalization_etale k m S q A
  revert hJ
  induction J using Finset.induction_on with
  | empty =>
      intro _
      have h0 : Ideal.map (algebraMap S A) (etaleChartCoordIdeal k m S (∅ : Finset (Fin m))) = ⊥ := by
        rw [etaleChartCoordIdeal_eq_span_image]
        simp
      have hker : (⊥ : Ideal A) = RingHom.ker (RingHom.id A) := by
        ext a
        simp [RingHom.mem_ker]
      have e : (A ⧸ (⊥ : Ideal A)) ≃+* A :=
        (Ideal.quotEquivOfEq hker).trans
          (RingHom.quotientKerEquivOfSurjective
            (show Function.Surjective (RingHom.id A) from fun a => ⟨a, rfl⟩))
      rw [h0, ringKrullDim_eq_of_ringEquiv e]
      simp
  | @insert j J' hjJ ih =>
      intro hJ
      have hJ' : ∀ i ∈ J', etaleChartCoord k m S i ∈ q := fun i hi =>
        hJ i (Finset.mem_insert_of_mem hi)
      have hjq : etaleChartCoord k m S j ∈ q := hJ j (Finset.mem_insert_self _ _)
      set I' := Ideal.map (algebraMap S A) (etaleChartCoordIdeal k m S J') with hI'
      have hR : IsRegularLocalRing (A ⧸ I') :=
        isRegularLocalRing_quotient_map_etaleChartCoordIdeal k m S q A J' hJ'
      set y : A := algebraMap S A (etaleChartCoord k m S j) with hy
      have hins : Ideal.map (algebraMap S A) (etaleChartCoordIdeal k m S (insert j J'))
          = I' ⊔ Ideal.span {y} := by
        rw [hI', hy, etaleChartCoordIdeal_eq_span_image, etaleChartCoordIdeal_eq_span_image, Finset.coe_insert,
          Set.image_insert_eq, Ideal.span_insert, Ideal.map_sup, Ideal.map_span, Ideal.map_span,
          Set.image_singleton]
        exact sup_comm _ _
      have hspan : Ideal.map (Ideal.Quotient.mk I') (Ideal.span {y})
          = Ideal.span {Ideal.Quotient.mk I' y} := by
        rw [Ideal.map_span, Set.image_singleton]
      have e := (Ideal.quotEquivOfEq hspan.symm).trans
        (DoubleQuot.quotQuotEquivQuotSup I' (Ideal.span {y}))
      have hdim1 : ringKrullDim
          (A ⧸ Ideal.map (algebraMap S A) (etaleChartCoordIdeal k m S (insert j J')))
          = ringKrullDim ((A ⧸ I') ⧸ Ideal.span {Ideal.Quotient.mk I' y}) := by
        rw [hins]
        exact (ringKrullDim_eq_of_ringEquiv e).symm
      have hmaxR : IsLocalRing.maximalIdeal (A ⧸ I')
          = Ideal.map (Ideal.Quotient.mk I') (IsLocalRing.maximalIdeal A) :=
        (IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk I')
          Ideal.Quotient.mk_surjective).symm
      have hy1 : Ideal.Quotient.mk I' y ∈ IsLocalRing.maximalIdeal (A ⧸ I') := by
        rw [hmaxR, hy]
        exact Ideal.mem_map_of_mem _
          ((IsLocalization.AtPrime.to_map_mem_maximal_iff A q (etaleChartCoord k m S j)
            inferInstance).mpr hjq)
      have hy2 : Ideal.Quotient.mk I' y ∉ IsLocalRing.maximalIdeal (A ⧸ I') ^ 2 := by
        rw [hmaxR, ← Ideal.map_pow]
        intro hcon
        have hcon2 : y ∈ Ideal.comap (Ideal.Quotient.mk I')
            (Ideal.map (Ideal.Quotient.mk I') (IsLocalRing.maximalIdeal A ^ 2)) := hcon
        rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
          ← RingHom.ker_eq_comap_bot, Ideal.mk_ker] at hcon2
        rw [hy, hI'] at hcon2
        exact algebraMap_etaleChartCoord_notMem_maximalIdeal_sq_sup k m S q A J' hJ' j hjJ hcon2
      have hstep :=
        IsRegularLocalRing.ringKrullDim_quotient_span_singleton_add_one hy1 hy2
      rw [hdim1, Finset.card_insert_of_notMem hjJ]
      have hcard : (((J'.card + 1 : ℕ)) : WithBot ℕ∞) = 1 + (J'.card : WithBot ℕ∞) := by
        push_cast
        ring
      rw [hcard, ← add_assoc, hstep]
      exact ih hJ'
end FunctorialResolution.EmbeddedResolution
