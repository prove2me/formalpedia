-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.le_iff_forall_stalkIdeal_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:04:54.03737+00:00
-- url     : https://prove2.me/submissions/1460df15-813a-46b5-be19-f5476373df1d

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisibility
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisorSmoothness
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinatePolynomialRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_OrderAtGenericPoint
import Theorems.Thm_Derivation_liftToLocalization_algebraMap
import Theorems.Thm_Derivation_mapToLocalization_algebraMap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_coordRingHom_X
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_ofCoords_map
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_basisDerivation_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInl_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInl_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInr_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInr_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheaf_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_pullbackCoord_def
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_eq_map_germ
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_mono
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
private theorem span_eq_top_of_forall_mem_basicOpen {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (s : Set Γ(X, U))
    (hcov : ∀ x : X, x ∈ U → ∃ t ∈ s, x ∈ X.basicOpen t) :
    Ideal.span s = ⊤ := by
  have hUeq : (⨆ f : s, X.basicOpen (f : Γ(X, U))) = U := by
    refine le_antisymm (iSup_le fun f => Scheme.basicOpen_le (X := X) (f : Γ(X, U)))
      (SetLike.le_def.mpr ?_)
    intro x hx
    obtain ⟨t, hts, hxt⟩ := hcov x hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨t, hts⟩, hxt⟩
  exact (IsAffineOpen.iSup_basicOpen_eq_self_iff hU).mp hUeq
private theorem exists_mul_mem_of_map_mem_map {R S : Type*} [CommRing R] [CommRing S]
    (g : R →+* S) (M : Submonoid R) (hlocal : @IsLocalization R _ M S _ g.toAlgebra)
    (b : Ideal R) (f : R) (hf : g f ∈ Ideal.map g b) :
    ∃ t ∈ M, t * f ∈ b := by
  let _ : Algebra R S := g.toAlgebra
  have : IsLocalization M S := hlocal
  have hf' : algebraMap R S f ∈ Ideal.map (algebraMap R S) b := hf
  obtain ⟨⟨y, m⟩, he⟩ := (IsLocalization.mem_map_algebraMap_iff (M := M) (S := S)).mp hf'
  rw [← map_mul] at he
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists (M := M) (S := S)).mp he
  refine ⟨(c : R) * (m : R), M.mul_mem c.2 m.2, ?_⟩
  have h3 : (c : R) * (m : R) * f = (c : R) * (y : R) := by rw [← hc]; ring
  rw [h3]
  exact b.mul_mem_left _ y.2
private theorem isUnit_map_of_mem_of_isLocalization {R S : Type*} [CommRing R] [CommRing S]
    (g : R →+* S) (M : Submonoid R) (hlocal : @IsLocalization R _ M S _ g.toAlgebra)
    (t : R) (ht : t ∈ M) : IsUnit (g t) := by
  let _ : Algebra R S := g.toAlgebra
  have : IsLocalization M S := hlocal
  have h1 : IsUnit (algebraMap R S t) := IsLocalization.map_units S (⟨t, ht⟩ : M)
  exact h1
private theorem mem_of_span_mul_mem_eq_top {R : Type*} [CommRing R] (b : Ideal R)
    (f : R) (h : Ideal.span {t : R | t * f ∈ b} = ⊤) : f ∈ b := by
  have hC : ∀ g ∈ Ideal.span {t : R | t * f ∈ b}, g * f ∈ b := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem x hx => exact hx
    | zero => simp
    | add x y hx hy ihx ihy => simpa [add_mul] using b.add_mem ihx ihy
    | smul a x hx ih => simpa [smul_eq_mul, mul_assoc] using b.mul_mem_left a ih
  have h1 : (1 : R) ∈ Ideal.span {t : R | t * f ∈ b} := by
    rw [h]; exact Submodule.mem_top
  simpa using hC 1 h1
variable {X : Scheme.{u}} {k : Type u} [Field k] (p : X ⟶ Spec (CommRingCat.of k))
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {X : Scheme.{u}} (I J : X.IdealSheafData) :
    I ≤ J ↔ ∀ x : X, stalkIdeal I x ≤ stalkIdeal J x := by
  refine ⟨fun h x => stalkIdeal_mono h x, fun h => ?_⟩
  rw [Scheme.IdealSheafData.le_def]
  intro U f hf
  have hU : IsAffineOpen U.1 := U.2
  have hlocal : ∀ (x : X) (hx : x ∈ U.1),
      @IsLocalization ↥Γ(X, U.1) _
        (IsAffineOpen.primeIdealOf hU ⟨x, hx⟩).asIdeal.primeCompl
        ↥(X.presheaf.stalk x) _ ((X.presheaf.germ U.1 x hx).hom.toAlgebra) := by
    intro x hx
    exact IsAffineOpen.isLocalization_stalk hU ⟨x, hx⟩
  have hbasic : ∀ (x : X) (hx : x ∈ U.1) (t : Γ(X, U.1)),
      IsUnit ((X.presheaf.germ U.1 x hx).hom t) → x ∈ X.basicOpen t := by
    intro x hx t ht
    exact (Scheme.mem_basicOpen X t x hx).mpr ht
  have key : ∀ (x : X) (hx : x ∈ U.1),
      ∃ t : Γ(X, U.1), t * f ∈ J.ideal U ∧ x ∈ X.basicOpen t := by
    intro x hx
    have hmemI : (X.presheaf.germ U.1 x hx).hom f ∈ stalkIdeal I x := by
      rw [stalkIdeal_eq_map_germ I x U hx]
      exact Ideal.mem_map_of_mem _ hf
    have hmem : (X.presheaf.germ U.1 x hx).hom f ∈
        Ideal.map (X.presheaf.germ U.1 x hx).hom (J.ideal U) := by
      have hh := h x hmemI
      rwa [stalkIdeal_eq_map_germ J x U hx] at hh
    obtain ⟨t, htM, htf⟩ := exists_mul_mem_of_map_mem_map (X.presheaf.germ U.1 x hx).hom
      (IsAffineOpen.primeIdealOf hU ⟨x, hx⟩).asIdeal.primeCompl (hlocal x hx) (J.ideal U) f hmem
    exact ⟨t, htf, hbasic x hx t (isUnit_map_of_mem_of_isLocalization
      (X.presheaf.germ U.1 x hx).hom _ (hlocal x hx) t htM)⟩
  have hspan : Ideal.span {t : Γ(X, U.1) | t * f ∈ J.ideal U} = ⊤ := by
    refine span_eq_top_of_forall_mem_basicOpen hU {t : Γ(X, U.1) | t * f ∈ J.ideal U}
      (fun x hx => ?_)
    obtain ⟨t, htf, hxt⟩ := key x hx
    exact ⟨t, htf, hxt⟩
  exact mem_of_span_mul_mem_eq_top (J.ideal U) f hspan
end FunctorialResolution.EmbeddedResolution
