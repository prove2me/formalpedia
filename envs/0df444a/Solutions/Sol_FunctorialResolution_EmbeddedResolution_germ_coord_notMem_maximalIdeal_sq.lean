-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.germ_coord_notMem_maximalIdeal_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:58:31.144713+00:00
-- url     : https://prove2.me/submissions/93d67262-5a31-42eb-b947-f38ce79d90fe

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisorRadical
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_GermRegularParameters
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinatePolynomialRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_RegularLocalRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_CoordinateIdealOrderOne
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_algebra_etale
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_coordRingHom_X
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_germ_mem_maximalIdeal_iff
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isRegularLocalRing_of_isLocalization_etale
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_linearIndependent_toCotangent_etaleChartCoord
import Theorems.Thm_IsRegularLocalRing_notMem_maximalIdeal_sq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleChart.coordRingHom_X



set_option autoImplicit false
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {X : Scheme.{u}} {k : Type u} [Field k] (p : X ⟶ Spec (CommRingCat.of k))
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {V : X.Opens} (hV : IsAffineOpen V) {n : ℕ}
    (c : EtaleChart p V n) (j : Fin n) (y : X) (hy : y ∈ V)
    (hmem : c.coord j ∈ (hV.primeIdealOf ⟨y, hy⟩).asIdeal) :
    (X.presheaf.germ V y hy).hom (c.coord j) ∉
      IsLocalRing.maximalIdeal (X.presheaf.stalk y) ^ 2 := by
  classical
  let instS : Algebra (CoordPolynomialRing k n) Γ(X, V) := c.algebra
  have instEt : Algebra.Etale (CoordPolynomialRing k n) Γ(X, V) :=
    EtaleChart.algebra_etale c hV
  let instAlg : Algebra Γ(X, V) (X.presheaf.stalk y) :=
    (X.presheaf.germ V y hy).hom.toAlgebra
  have hloc : IsLocalization (hV.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl
      (X.presheaf.stalk y) := hV.isLocalization_stalk ⟨y, hy⟩
  have hreg : IsRegularLocalRing (X.presheaf.stalk y) :=
    isRegularLocalRing_of_isLocalization_etale k n Γ(X, V)
      (hV.primeIdealOf ⟨y, hy⟩).asIdeal (X.presheaf.stalk y)
  have hcoord : ∀ i : Fin n, etaleChartCoord k n Γ(X, V) i = c.coord i := fun i =>
    EtaleChart.coordRingHom_X c i
  have hJ : ∀ i ∈ ({j} : Finset (Fin n)),
      etaleChartCoord k n Γ(X, V) i ∈ (hV.primeIdealOf ⟨y, hy⟩).asIdeal := by
    intro i hi
    have hij : i = j := Finset.mem_singleton.mp hi
    rw [hij, hcoord j]
    exact hmem
  have hJA : ∀ i ∈ ({j} : Finset (Fin n)),
      algebraMap Γ(X, V) (X.presheaf.stalk y) (etaleChartCoord k n Γ(X, V) i)
        ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk y) := by
    intro i hi
    have hij : i = j := Finset.mem_singleton.mp hi
    rw [hij, hcoord j]
    exact (germ_mem_maximalIdeal_iff hV y hy (c.coord j)).mpr hmem
  have hli := linearIndependent_toCotangent_etaleChartCoord k n Γ(X, V)
    (hV.primeIdealOf ⟨y, hy⟩).asIdeal (X.presheaf.stalk y) ({j} : Finset (Fin n)) hJ hJA
  have hnot := IsRegularLocalRing.notMem_maximalIdeal_sq
    (fun i : {x : Fin n // x ∈ ({j} : Finset (Fin n))} =>
      algebraMap Γ(X, V) (X.presheaf.stalk y) (etaleChartCoord k n Γ(X, V) (i : Fin n)))
    (fun i => hJA (i : Fin n) i.2) hli ⟨j, Finset.mem_singleton_self j⟩
  intro hcon
  have h2 : algebraMap Γ(X, V) (X.presheaf.stalk y) (etaleChartCoord k n Γ(X, V) j)
      ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk y) ^ 2 := by
    rw [hcoord j]
    exact hcon
  exact hnot h2
end FunctorialResolution.EmbeddedResolution
