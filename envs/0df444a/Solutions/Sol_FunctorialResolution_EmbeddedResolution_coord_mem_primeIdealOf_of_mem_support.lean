-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.coord_mem_primeIdealOf_of_mem_support
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:00:41.538933+00:00
-- url     : https://prove2.me/submissions/814c8bf8-9d3d-4a9f-abbc-6efb8ca1f90a

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisibility
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisorSmoothness
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinatePolynomialRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_OrderAtGenericPoint
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_eq_span_germ_coord
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_mem_support_iff_stalkIdeal_ne_top


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {X : Scheme.{u}} {k : Type u} [Field k] (p : X ⟶ Spec (CommRingCat.of k))
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {V : X.Opens} (hV : IsAffineOpen V) {n : ℕ}
    (c : EtaleChart p V n) (j : Fin n) (D : X.IdealSheafData)
    (hD : restrictIdeal D V = c.coordIdeal {j}) (y : X) (hy : y ∈ V) (hys : y ∈ D.support) :
    c.coord j ∈ (hV.primeIdealOf ⟨y, hy⟩).asIdeal := by
  by_contra hcon
  let _ : Algebra (Γ(X, V)) (X.presheaf.stalk y) :=
    (X.presheaf.germ V y hy).hom.toAlgebra
  have : IsLocalization.AtPrime (X.presheaf.stalk y)
      (hV.primeIdealOf ⟨y, hy⟩).asIdeal := hV.isLocalization_stalk ⟨y, hy⟩
  have hunit : IsUnit ((X.presheaf.germ V y hy).hom (c.coord j)) :=
    IsLocalization.map_units (S := X.presheaf.stalk y)
      (M := (hV.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl) ⟨c.coord j, hcon⟩
  refine (mem_support_iff_stalkIdeal_ne_top D y).mp hys ?_
  rw [stalkIdeal_eq_span_germ_coord p hV c j D hD y hy]
  exact Ideal.span_singleton_eq_top.mpr hunit
end FunctorialResolution.EmbeddedResolution
