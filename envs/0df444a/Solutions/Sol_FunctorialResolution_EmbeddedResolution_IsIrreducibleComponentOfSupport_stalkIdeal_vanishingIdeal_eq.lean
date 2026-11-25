-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.IsIrreducibleComponentOfSupport.stalkIdeal_vanishingIdeal_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:37:54.099103+00:00
-- url     : https://prove2.me/submissions/9145ab33-f97c-43fd-8102-1f2e3d1680a9

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
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_IsIrreducibleComponentOfSupport_exists_affineOpen_etaleChart_coordIdeal

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
open FunctorialResolution.EmbeddedResolution.IsIrreducibleComponentOfSupport
variable {X : Scheme.{u}} {D : X.IdealSheafData} {C : Set X}
variable {k : Type u} [Field k]
namespace FunctorialResolution.EmbeddedResolution.IsIrreducibleComponentOfSupport
theorem _root_.solution [TopologicalSpace.NoetherianSpace ↥X]
    (hC : IsIrreducibleComponentOfSupport D C) (p : X ⟶ Spec (CommRingCat.of k))
    (hloc : ∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U) (n : ℕ) (c : EtaleChart p U n),
      restrictIdeal D U = ⊤ ∨ ∃ j : Fin n, restrictIdeal D U = c.coordIdeal {j})
    (x : X) (hx : x ∈ C) :
    stalkIdeal (Scheme.IdealSheafData.vanishingIdeal
      (⟨C, hC.isClosed⟩ : TopologicalSpace.Closeds ↥X)) x = stalkIdeal D x := by
  obtain ⟨V, hV, hxV, n, c, j, -, -, -, -, hstalk⟩ := hC.exists_affineOpen_etaleChart_coordIdeal p hloc x hx
  exact hstalk x hxV
end FunctorialResolution.EmbeddedResolution.IsIrreducibleComponentOfSupport
