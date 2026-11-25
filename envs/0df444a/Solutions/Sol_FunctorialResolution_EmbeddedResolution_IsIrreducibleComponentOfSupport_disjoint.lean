-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.IsIrreducibleComponentOfSupport.disjoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:15:05.278697+00:00
-- url     : https://prove2.me/submissions/f7066d35-c31c-4c97-88c9-fe946ceea999

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_ClopenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisorSmoothness
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_PowerContainmentAndOrderLocus
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_OrderAtGenericPoint
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IrreducibleComponentsOfSupport
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_IsIrreducibleComponentOfSupport_closure_genericPoint
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_IsIrreducibleComponentOfSupport_genericPoint_specializes
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_IsIrreducibleComponentOfSupport_genericPoint_mem_support
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_mem_support_iff_ideal_le_primeIdealOf
import Theorems.Thm_Derivation_liftToLocalization_algebraMap
import Theorems.Thm_Derivation_mapToLocalization_algebraMap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_coordRingHom_X
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_ideal_eq_span_coord
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_ofCoords_map
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_basisDerivation_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInl_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInl_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInr_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInr_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheaf_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_exists_etaleChart_genericPoint_mem
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_mem_support_iff_stalkIdeal_le_maximalIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_primeIdealOf_eq_comap_span_germ_coord
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_pullbackCoord_def
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_eq_map_germ
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
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
private theorem exists_fromSpec_mem_and_primeIdealOf_eq {X : Scheme.{u}} {V : X.Opens} (hV : IsAffineOpen V)
    (P : PrimeSpectrum Γ(X, V)) :
    ∃ hz : hV.fromSpec.base P ∈ V, hV.primeIdealOf ⟨hV.fromSpec.base P, hz⟩ = P := by
  have hz : hV.fromSpec.base P ∈ V := by
    have h : hV.fromSpec.base P ∈ Set.range hV.fromSpec.base := ⟨P, rfl⟩
    rwa [hV.range_fromSpec] at h
  refine ⟨hz, hV.fromSpec.isOpenEmbedding.injective ?_⟩
  rw [hV.fromSpec_primeIdealOf]
private theorem mem_support_iff_ideal_le_primeIdealOf {X : Scheme.{u}} (I : X.IdealSheafData)
    {V : X.Opens} (hV : IsAffineOpen V) {x : ↥X} (hx : x ∈ V) :
    x ∈ I.support ↔ I.ideal ⟨V, hV⟩ ≤ (hV.primeIdealOf ⟨x, hx⟩).asIdeal := by
  let _ : Algebra ↑Γ(X, V) ↑(X.presheaf.stalk x) :=
    RingHom.toAlgebra (X.presheaf.germ V x hx).hom
  have : IsLocalization.AtPrime ↑(X.presheaf.stalk x) (hV.primeIdealOf ⟨x, hx⟩).asIdeal :=
    hV.isLocalization_stalk ⟨x, hx⟩
  have hcomap : Ideal.comap (X.presheaf.germ V x hx).hom
      (IsLocalRing.maximalIdeal ↑(X.presheaf.stalk x))
      = (hV.primeIdealOf ⟨x, hx⟩).asIdeal := by
    have h := IsLocalization.AtPrime.under_maximalIdeal (R := ↑Γ(X, V))
      (S := ↑(X.presheaf.stalk x)) (I := (hV.primeIdealOf ⟨x, hx⟩).asIdeal)
    exact h
  rw [mem_support_iff_stalkIdeal_le_maximalIdeal, stalkIdeal_eq_map_germ I x ⟨V, hV⟩ hx,
    Ideal.map_le_iff_le_comap]
  exact iff_of_eq (congrArg (fun J => I.ideal ⟨V, hV⟩ ≤ J) hcomap)
namespace IsIrreducibleComponentOfSupport
variable {X : Scheme.{u}} {D : X.IdealSheafData} {C : Set X}
end IsIrreducibleComponentOfSupport
namespace IsIrreducibleComponentOfSupport
variable {X : Scheme.{u}} {D : X.IdealSheafData} {C : Set X}
variable {k : Type u} [Field k]
end IsIrreducibleComponentOfSupport
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.IsIrreducibleComponentOfSupport
variable {X : Scheme.{u}} {D : X.IdealSheafData} {C : Set X}
variable {k : Type u} [Field k]
namespace FunctorialResolution.EmbeddedResolution.IsIrreducibleComponentOfSupport
theorem _root_.solution {C' : Set X} (hC : IsIrreducibleComponentOfSupport D C) (hC' : IsIrreducibleComponentOfSupport D C')
    (p : X ⟶ Spec (CommRingCat.of k))
    (hloc : ∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U) (n : ℕ) (c : EtaleChart p U n),
      restrictIdeal D U = ⊤ ∨ ∃ j : Fin n, restrictIdeal D U = c.coordIdeal {j})
    (hne : C ≠ C') : Disjoint C C' := by
  rw [Set.disjoint_left]
  intro y hyC hyC'
  apply hne
  obtain ⟨V, hV, hyV, hetaV, n, c, j, hD, hspec, hetas, hmin⟩ :=
    exists_etaleChart_genericPoint_mem p D hloc hC.isIrreducible hC.subset_support hC.maximal y hyC
  have hspec' : hC'.isIrreducible.genericPoint ⤳ y := hC'.genericPoint_specializes hyC'
  have heta'V : hC'.isIrreducible.genericPoint ∈ V := hspec'.mem_open V.isOpen hyV
  have heta's : hC'.isIrreducible.genericPoint ∈ D.support := hC'.genericPoint_mem_support
  have hmin' : ∀ P : Ideal Γ(X, V), P.IsPrime → c.coord j ∈ P →
      P ≤ (hV.primeIdealOf ⟨hC'.isIrreducible.genericPoint, heta'V⟩).asIdeal →
      P = (hV.primeIdealOf ⟨hC'.isIrreducible.genericPoint, heta'V⟩).asIdeal := by
    intro P hP hcoord hle
    obtain ⟨hz, hzP⟩ := exists_fromSpec_mem_and_primeIdealOf_eq hV ⟨P, hP⟩
    have hzs : hV.fromSpec.base (⟨P, hP⟩ : PrimeSpectrum Γ(X, V)) ∈ D.support := by
      rw [mem_support_iff_ideal_le_primeIdealOf D hV hz, hzP]
      rw [c.ideal_eq_span_coord hV D {j} hD, Ideal.span_le]
      rintro f ⟨i, hi, rfl⟩
      have hij : i = j := by simpa using hi
      subst hij
      exact hcoord
    have hsp : (⟨P, hP⟩ : PrimeSpectrum Γ(X, V)) ⤳
        hV.primeIdealOf ⟨hC'.isIrreducible.genericPoint, heta'V⟩ := by
      rw [specializes_iff_mem_closure, PrimeSpectrum.closure_singleton,
        PrimeSpectrum.mem_zeroLocus]
      exact hle
    have hspz : hV.fromSpec.base (⟨P, hP⟩ : PrimeSpectrum Γ(X, V)) ⤳
        hC'.isIrreducible.genericPoint := by
      have hmapped := hsp.map hV.fromSpec.base.hom.continuous
      rwa [hV.fromSpec_primeIdealOf] at hmapped
    have hclo : closure {hV.fromSpec.base (⟨P, hP⟩ : PrimeSpectrum Γ(X, V))} = C' := by
      refine hC'.maximal _ isIrreducible_singleton.closure ?_ ?_
      · have h1 : {hC'.isIrreducible.genericPoint} ⊆
            closure {hV.fromSpec.base (⟨P, hP⟩ : PrimeSpectrum Γ(X, V))} :=
          Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hspz)
        have h2 := closure_mono h1
        rw [closure_closure] at h2
        rw [← hC'.closure_genericPoint]
        exact h2
      · have h3 : closure {hV.fromSpec.base (⟨P, hP⟩ : PrimeSpectrum Γ(X, V))}
            ⊆ closure ((D.support : Set ↥X)) :=
          closure_mono (Set.singleton_subset_iff.mpr hzs)
        rwa [D.support.isClosed.closure_eq] at h3
    have hzC' : hV.fromSpec.base (⟨P, hP⟩ : PrimeSpectrum Γ(X, V)) ∈ C' := by
      rw [← hclo]; exact subset_closure (Set.mem_singleton _)
    have hzeq : hV.fromSpec.base (⟨P, hP⟩ : PrimeSpectrum Γ(X, V))
        = hC'.isIrreducible.genericPoint :=
      (hspz.antisymm (hC'.genericPoint_specializes hzC')).eq
    have hfin : hV.primeIdealOf ⟨hC'.isIrreducible.genericPoint, heta'V⟩
        = (⟨P, hP⟩ : PrimeSpectrum Γ(X, V)) := by
      rw [← hzP]
      congr 1
      exact Subtype.ext hzeq.symm
    exact (congrArg PrimeSpectrum.asIdeal hfin).symm
  have e1 := primeIdealOf_eq_comap_span_germ_coord p hV c j D hD y
    hC.isIrreducible.genericPoint hyV hetaV hspec hetas hmin
  have e2 := primeIdealOf_eq_comap_span_germ_coord p hV c j D hD y
    hC'.isIrreducible.genericPoint hyV heta'V hspec' heta's hmin'
  have hP : hV.primeIdealOf ⟨hC.isIrreducible.genericPoint, hetaV⟩
      = hV.primeIdealOf ⟨hC'.isIrreducible.genericPoint, heta'V⟩ :=
    PrimeSpectrum.ext (e1.trans e2.symm)
  have hpts : hC.isIrreducible.genericPoint = hC'.isIrreducible.genericPoint := by
    have h := congrArg (fun q => hV.fromSpec.base q) hP
    simpa only [hV.fromSpec_primeIdealOf] using h
  rw [← hC.closure_genericPoint, ← hC'.closure_genericPoint, hpts]
end FunctorialResolution.EmbeddedResolution.IsIrreducibleComponentOfSupport
