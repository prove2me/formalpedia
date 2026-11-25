-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.primeIdealOf_eq_comap_span_germ_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:05:28.885509+00:00
-- url     : https://prove2.me/submissions/6a12aed6-6c23-407b-92ea-9887be23c423

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisibility
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisorSmoothness
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinatePolynomialRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_OrderAtGenericPoint
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coord_mem_primeIdealOf_of_mem_support
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_algebra_etale
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_coordRingHom_X
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_etaleChartCoord_def
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isPrime_span_singleton_algebraMap_etaleChartCoord
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleChart.coordRingHom_X


section
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
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
variable {X : Scheme.{u}} {k : Type u} [Field k] (p : X ⟶ Spec (CommRingCat.of k))
private theorem isUnit_germ_iff_notMem_primeIdealOf {Y : Scheme.{u}} {W : Y.Opens}
    (hW : IsAffineOpen W) (y : Y) (hy : y ∈ W) (f : Γ(Y, W)) :
    IsUnit ((Y.presheaf.germ W y hy).hom f) ↔ f ∉ (hW.primeIdealOf ⟨y, hy⟩).asIdeal := by
  let _ : Algebra (Γ(Y, W)) (Y.presheaf.stalk y) := (Y.presheaf.germ W y hy).hom.toAlgebra
  have : IsLocalization.AtPrime (Y.presheaf.stalk y) (hW.primeIdealOf ⟨y, hy⟩).asIdeal :=
    hW.isLocalization_stalk ⟨y, hy⟩
  constructor
  · intro hu hmem
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (↥(Y.presheaf.stalk y))
      (hW.primeIdealOf ⟨y, hy⟩).asIdeal f).mp hu hmem
  · intro hmem
    exact IsLocalization.map_units (S := Y.presheaf.stalk y)
      (M := (hW.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl) ⟨f, hmem⟩
private theorem primeIdealOf_le_of_specializes {Y : Scheme.{u}} {W : Y.Opens}
    (hW : IsAffineOpen W) (a b : Y) (ha : a ∈ W) (hb : b ∈ W) (h : a ⤳ b) :
    (hW.primeIdealOf ⟨a, ha⟩).asIdeal ≤ (hW.primeIdealOf ⟨b, hb⟩).asIdeal := by
  intro f hf
  by_contra hcon
  have hb' : b ∈ Y.basicOpen f :=
    (Scheme.mem_basicOpen Y f b hb).mpr ((isUnit_germ_iff_notMem_primeIdealOf hW b hb f).mpr hcon)
  have ha' : a ∈ Y.basicOpen f := h.mem_open (Y.basicOpen f).isOpen hb'
  exact ((isUnit_germ_iff_notMem_primeIdealOf hW a ha f).mp
    ((Scheme.mem_basicOpen Y f a ha).mp ha')) hf
private theorem isPrime_span_germ_coord {Y : Scheme.{u}} {K : Type u} [Field K]
    {pr : Y ⟶ Spec (CommRingCat.of K)} {W : Y.Opens} (hW : IsAffineOpen W) {n : ℕ}
    (c : EtaleChart pr W n) (j : Fin n) (y : Y) (hy : y ∈ W)
    (hcoord : c.coord j ∈ (hW.primeIdealOf ⟨y, hy⟩).asIdeal) :
    (Ideal.span ({(Y.presheaf.germ W y hy).hom (c.coord j)} :
      Set (Y.presheaf.stalk y))).IsPrime := by
  let instPoly : Algebra (MvPolynomial (ULift.{u} (Fin n)) K) (Γ(Y, W)) := c.algebra
  have instEt : Algebra.Etale (MvPolynomial (ULift.{u} (Fin n)) K) (Γ(Y, W)) :=
    c.algebra_etale hW
  let instAlg : Algebra (Γ(Y, W)) (Y.presheaf.stalk y) :=
    (Y.presheaf.germ W y hy).hom.toAlgebra
  have instPrime : ((hW.primeIdealOf ⟨y, hy⟩).asIdeal).IsPrime :=
    (hW.primeIdealOf ⟨y, hy⟩).isPrime
  have instLoc : IsLocalization.AtPrime (Y.presheaf.stalk y)
      (hW.primeIdealOf ⟨y, hy⟩).asIdeal := hW.isLocalization_stalk ⟨y, hy⟩
  have hcoordeq : etaleChartCoord K n (Γ(Y, W)) j = c.coord j := by
    rw [etaleChartCoord_def]
    exact EtaleChart.coordRingHom_X c j
  have h := isPrime_span_singleton_algebraMap_etaleChartCoord K n (Γ(Y, W))
    ((hW.primeIdealOf ⟨y, hy⟩).asIdeal) (Y.presheaf.stalk y) j
    (by rw [hcoordeq]; exact hcoord)
  rw [hcoordeq] at h
  exact h
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {X : Scheme.{u}} {k : Type u} [Field k] (p : X ⟶ Spec (CommRingCat.of k))
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {V : X.Opens} (hV : IsAffineOpen V) {n : ℕ}
    (c : EtaleChart p V n) (j : Fin n) (D : X.IdealSheafData)
    (hD : restrictIdeal D V = c.coordIdeal {j}) (x η : X) (hx : x ∈ V) (hη : η ∈ V)
    (hspec : η ⤳ x) (hηs : η ∈ D.support)
    (hmin : ∀ P : Ideal Γ(X, V), P.IsPrime → c.coord j ∈ P →
      P ≤ (hV.primeIdealOf ⟨η, hη⟩).asIdeal → P = (hV.primeIdealOf ⟨η, hη⟩).asIdeal) :
    (hV.primeIdealOf ⟨η, hη⟩).asIdeal =
      Ideal.comap (X.presheaf.germ V x hx).hom
        (Ideal.span ({(X.presheaf.germ V x hx).hom (c.coord j)} :
          Set (X.presheaf.stalk x))) := by
  have hcoordq : c.coord j ∈ (hV.primeIdealOf ⟨η, hη⟩).asIdeal :=
    coord_mem_primeIdealOf_of_mem_support p hV c j D hD η hη hηs
  have hqle : (hV.primeIdealOf ⟨η, hη⟩).asIdeal ≤ (hV.primeIdealOf ⟨x, hx⟩).asIdeal :=
    primeIdealOf_le_of_specializes hV η x hη hx hspec
  have hsp : (Ideal.span ({(X.presheaf.germ V x hx).hom (c.coord j)} :
      Set (X.presheaf.stalk x))).IsPrime :=
    isPrime_span_germ_coord hV c j x hx (hqle hcoordq)
  have hPprime : (Ideal.comap (X.presheaf.germ V x hx).hom
      (Ideal.span ({(X.presheaf.germ V x hx).hom (c.coord j)} :
        Set (X.presheaf.stalk x)))).IsPrime := inferInstance
  have htP : c.coord j ∈ Ideal.comap (X.presheaf.germ V x hx).hom
      (Ideal.span ({(X.presheaf.germ V x hx).hom (c.coord j)} :
        Set (X.presheaf.stalk x))) := by
    rw [Ideal.mem_comap]
    exact Ideal.mem_span_singleton_self _
  have hmapspan : Ideal.map (X.presheaf.germ V x hx).hom
      (Ideal.span ({c.coord j} : Set Γ(X, V)))
      = Ideal.span ({(X.presheaf.germ V x hx).hom (c.coord j)} :
        Set (X.presheaf.stalk x)) := by
    rw [Ideal.map_span, Set.image_singleton]
  have hloc : @IsLocalization ↥Γ(X, V) _ (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
      ↥(X.presheaf.stalk x) _ ((X.presheaf.germ V x hx).hom.toAlgebra) :=
    hV.isLocalization_stalk ⟨x, hx⟩
  have hPle : Ideal.comap (X.presheaf.germ V x hx).hom
      (Ideal.span ({(X.presheaf.germ V x hx).hom (c.coord j)} :
        Set (X.presheaf.stalk x)))
      ≤ (hV.primeIdealOf ⟨η, hη⟩).asIdeal := by
    intro a ha
    rw [Ideal.mem_comap, ← hmapspan] at ha
    obtain ⟨s, hs, hsa⟩ := exists_mul_mem_of_map_mem_map (X.presheaf.germ V x hx).hom
      (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl hloc
      (Ideal.span ({c.coord j} : Set Γ(X, V))) a ha
    have hs' : s ∉ (hV.primeIdealOf ⟨x, hx⟩).asIdeal := hs
    have hsq : s ∉ (hV.primeIdealOf ⟨η, hη⟩).asIdeal := fun hcon => hs' (hqle hcon)
    have hle : Ideal.span ({c.coord j} : Set Γ(X, V)) ≤ (hV.primeIdealOf ⟨η, hη⟩).asIdeal :=
      (Ideal.span_singleton_le_iff_mem _).mpr hcoordq
    exact ((hV.primeIdealOf ⟨η, hη⟩).isPrime.mem_or_mem (hle hsa)).resolve_left hsq
  exact (hmin _ hPprime htP hPle).symm
end FunctorialResolution.EmbeddedResolution
