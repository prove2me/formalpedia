-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.ideal_le_pow_of_restrictIdeal_eq_coordIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:02:04.203859+00:00
-- url     : https://prove2.me/submissions/90fd1d08-ccdc-44c7-9d44-98c62374b5c5

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_ClopenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisorSmoothness
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinatePolynomialRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateSubscheme
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealOrderDecrease
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheafOrderDecrease
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_PowerContainmentAndOrderLocus
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isRadical_ideal_of_restrictIdeal_eq_coordIdeal
import Theorems.Thm_Derivation_liftToLocalization_algebraMap
import Theorems.Thm_Derivation_mapToLocalization_algebraMap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_algebra_formallyEtale
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_coordRingHom_X
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_etaleCoordinates_coord
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_ideal_eq_span_coord
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_isScalarTower
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_ofCoords_map
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_basisDerivation_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInl_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInl_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInr_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInr_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealIterate_le_of_le
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealIterate_succ
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealIterate_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheaf_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivation_apply_mem_derivIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_mem_pow_succ_of_deriv_mem_pow
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_mem_support_iff_stalkIdeal_le_maximalIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_pullbackCoord_def
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_eq_map_germ
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_support_derivIdealSheafIterate_eq_orderAtLeastLocus
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
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInl_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInl_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInr_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInr_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_ideal
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_zero
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheaf_ideal
attribute [local simp] FunctorialResolution.EmbeddedResolution.pullbackCoord_def


section
universe u
open AlgebraicGeometry CategoryTheory TopologicalSpace
namespace FunctorialResolution.EmbeddedResolution
private theorem mem_support_iff_ideal_le_primeIdealOf_of_isAffineOpen {X : Scheme.{u}} (I : X.IdealSheafData) {U : X.Opens}
    (hU : IsAffineOpen U) (x : U) :
    (x : X) ∈ I.support ↔ I.ideal ⟨U, hU⟩ ≤ (hU.primeIdealOf x).asIdeal := by
  have := hU.isLocalization_stalk x
  rw [mem_support_iff_stalkIdeal_le_maximalIdeal, stalkIdeal_eq_map_germ I (x : X) ⟨U, hU⟩ x.2]
  constructor
  · intro hle y hy
    have h2 : (X.presheaf.germ U (x : X) x.2).hom y ∈
        IsLocalRing.maximalIdeal ↑(X.presheaf.stalk (x : X)) := hle (Ideal.mem_map_of_mem _ hy)
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff
      (X.presheaf.stalk (x : X)) (hU.primeIdealOf x).asIdeal y).mp h2
  · intro hle
    rw [Ideal.map_le_iff_le_comap]
    intro y hy
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff
      (X.presheaf.stalk (x : X)) (hU.primeIdealOf x).asIdeal y).mpr (hle hy)
private theorem exists_point_primeIdealOf_eq {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (q : PrimeSpectrum Γ(X, U)) : ∃ x : U, hU.primeIdealOf x = q := by
  have hmem : hU.fromSpec.base q ∈ U := by
    have h1 : hU.fromSpec.base q ∈ Set.range hU.fromSpec.base := ⟨q, rfl⟩
    rw [hU.range_fromSpec] at h1
    exact h1
  refine ⟨⟨hU.fromSpec.base q, hmem⟩, ?_⟩
  have hinj : Function.Injective hU.fromSpec.base := hU.fromSpec.isOpenEmbedding.injective
  apply hinj
  exact hU.fromSpec_primeIdealOf ⟨hU.fromSpec.base q, hmem⟩
private theorem ideal_le_of_support_subset {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (Z J : X.IdealSheafData) (hrad : (Z.ideal ⟨U, hU⟩).IsRadical)
    (hsupp : ∀ x : X, x ∈ Z.support → x ∈ U → x ∈ J.support) :
    J.ideal ⟨U, hU⟩ ≤ Z.ideal ⟨U, hU⟩ := by
  have hrad' : (Z.ideal ⟨U, hU⟩).radical = Z.ideal ⟨U, hU⟩ := hrad.radical
  rw [← hrad', Ideal.radical_eq_sInf]
  refine le_sInf ?_
  rintro q ⟨hq1, hq2⟩
  obtain ⟨x, hxq⟩ := exists_point_primeIdealOf_eq hU ⟨q, hq2⟩
  have hxq' : (hU.primeIdealOf x).asIdeal = q := congrArg PrimeSpectrum.asIdeal hxq
  have hxZ : (x : X) ∈ Z.support := by
    refine (mem_support_iff_ideal_le_primeIdealOf_of_isAffineOpen Z hU x).mpr ?_
    rw [hxq']
    exact hq1
  have hxJ := hsupp (x : X) hxZ x.2
  have hfin := (mem_support_iff_ideal_le_primeIdealOf_of_isAffineOpen J hU x).mp hxJ
  rw [hxq'] at hfin
  exact hfin
private theorem isUnit_natCast_of_algebra_of_charZero (k : Type*) [Field k] [CharZero k]
    (R : Type*) [CommRing R] [Algebra k R] {r : ℕ} (hr : 1 ≤ r) : IsUnit ((r : ℕ) : R) := by
  have h0 : ((r : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h1 : ((r : ℕ) : R) = algebraMap k R ((r : ℕ) : k) := (map_natCast (algebraMap k R) r).symm
  rw [h1]
  exact IsUnit.map (algebraMap k R) (IsUnit.mk0 ((r : ℕ) : k) h0)
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
universe u
open AlgebraicGeometry CategoryTheory TopologicalSpace
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {X : Scheme.{u}} {k : Type u} [Field k] [CharZero k]
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] {U : X.Opens}
    (hU : IsAffineOpen U) {n : ℕ} (c : EtaleChart p U n) (Z : X.IdealSheafData)
    (S : Finset (Fin n)) (h : restrictIdeal Z U = c.coordIdeal S) (m : ℕ)
    (I : X.IdealSheafData)
    (hord : ∀ x : X, x ∈ Z.support → x ∈ U → x ∈ orderAtLeastLocus I m) :
    I.ideal ⟨U, hU⟩ ≤ Z.ideal ⟨U, hU⟩ ^ m := by
  classical
  rcases Nat.eq_zero_or_pos m with hm0 | hm
  · subst hm0
    rw [pow_zero, Ideal.one_eq_top]
    exact le_top
  let algR : Algebra k Γ(X, U) := sectionsAlgebra k p U
  let algP : Algebra (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, U) := c.algebra
  have htower : IsScalarTower k (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, U) := c.isScalarTower
  have hfet : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, U) :=
    c.algebra_formallyEtale hU
  let xs : {i : Fin n // i ∈ S} → Γ(X, U) := fun i => c.coord i.1
  let Ds : {i : Fin n // i ∈ S} → Derivation k Γ(X, U) Γ(X, U) :=
    fun i => EtaleCoordinates.partialDeriv k (ULift.{u} (Fin n)) Γ(X, U) (ULift.up i.1)
  have hD : ∀ i j : {i : Fin n // i ∈ S}, Ds i (xs j) = if i = j then 1 else 0 := by
    intro i j
    show (EtaleCoordinates.partialDeriv k (ULift.{u} (Fin n)) Γ(X, U) (ULift.up i.1))
        (c.coord j.1) = if i = j then 1 else 0
    rw [← c.etaleCoordinates_coord j.1, EtaleCoordinates.partialDeriv_coord]
    have hiff : (ULift.up.{u} i.1 = ULift.up.{u} j.1) ↔ i = j := by
      constructor
      · intro hh
        exact Subtype.ext (congrArg ULift.down hh)
      · intro hh
        rw [hh]
    by_cases hij : i = j
    · rw [if_pos (hiff.mpr hij), if_pos hij]
    · rw [if_neg (fun hh => hij (hiff.mp hh)), if_neg hij]
  have hrange : Set.range xs = c.coord '' (S : Set (Fin n)) := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.1, i.2, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩
  have hspan : Ideal.span (Set.range xs) = Z.ideal ⟨U, hU⟩ := by
    rw [hrange, c.ideal_eq_span_coord hU Z S h]
  have hunit : ∀ r : ℕ, 1 ≤ r → IsUnit ((r : ℕ) : Γ(X, U)) := by
    intro r hr
    exact isUnit_natCast_of_algebra_of_charZero k Γ(X, U) hr
  have hbase : derivIdealIterate k (m - 1) (I.ideal ⟨U, hU⟩) ≤ Z.ideal ⟨U, hU⟩ := by
    have h1 : (derivIdealSheafIterate k p (m - 1) I).ideal ⟨U, hU⟩ ≤ Z.ideal ⟨U, hU⟩ := by
      refine ideal_le_of_support_subset hU Z (derivIdealSheafIterate k p (m - 1) I)
        (isRadical_ideal_of_restrictIdeal_eq_coordIdeal p hU c Z S h) ?_
      intro y hy hyU
      have h2 : ((derivIdealSheafIterate k p (m - 1) I).support : Set X) = orderAtLeastLocus I m :=
        support_derivIdealSheafIterate_eq_orderAtLeastLocus k p I hm
      have h3 : y ∈ orderAtLeastLocus I m := hord y hy hyU
      rw [← h2] at h3
      exact h3
    calc derivIdealIterate k (m - 1) (I.ideal ⟨U, hU⟩)
        = (derivIdealSheafIterate k p (m - 1) I).ideal ⟨U, hU⟩ :=
          (derivIdealSheafIterate_ideal k p (m - 1) I ⟨U, hU⟩).symm
      _ ≤ Z.ideal ⟨U, hU⟩ := h1
  have key : ∀ j : ℕ, 1 ≤ j → j ≤ m →
      derivIdealIterate k (m - j) (I.ideal ⟨U, hU⟩) ≤ Z.ideal ⟨U, hU⟩ ^ j := by
    intro j
    induction j with
    | zero => intro hj; exact absurd hj (by omega)
    | succ j ih =>
      intro _ hjm
      rcases Nat.eq_zero_or_pos j with hj0 | hj0
      · subst hj0
        simpa using hbase
      · intro f hf
        have hmem1 : f ∈ derivIdealIterate k (m - j) (I.ideal ⟨U, hU⟩) :=
          derivIdealIterate_le_of_le k (show m - (j + 1) ≤ m - j by omega) _ hf
        have hfW : f ∈ Z.ideal ⟨U, hU⟩ ^ j := ih hj0 (by omega) hmem1
        have hdf : ∀ i : {i : Fin n // i ∈ S}, (Ds i) f ∈ Z.ideal ⟨U, hU⟩ ^ j := by
          intro i
          refine ih hj0 (by omega) ?_
          have h4 : (Ds i) f ∈ derivIdeal k (derivIdealIterate k (m - (j + 1)) (I.ideal ⟨U, hU⟩)) :=
            derivation_apply_mem_derivIdeal k _ (Ds i) hf
          rw [← derivIdealIterate_succ] at h4
          exact derivIdealIterate_le_of_le k (show m - (j + 1) + 1 ≤ m - j by omega) _ h4
        have hf' : f ∈ Ideal.span (Set.range xs) ^ j := by rw [hspan]; exact hfW
        have hdf' : ∀ i : {i : Fin n // i ∈ S}, (Ds i) f ∈ Ideal.span (Set.range xs) ^ j := by
          intro i
          rw [hspan]
          exact hdf i
        have hres := mem_pow_succ_of_deriv_mem_pow k xs Ds hD (hunit j hj0) hf' hdf'
        rw [hspan] at hres
        exact hres
  have hfin := key m hm le_rfl
  rw [Nat.sub_self, derivIdealIterate_zero] at hfin
  exact hfin
end FunctorialResolution.EmbeddedResolution
