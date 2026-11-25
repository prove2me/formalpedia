-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.EtaleChart.restrictToSubscheme_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:22:58.353602+00:00
-- url     : https://prove2.me/submissions/1aa87f07-d97e-4553-8f4f-6e3bbb90b847

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateSubscheme
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_coord_def
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_ofCoords_map
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_coord_def
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleChart.ofCoords_map



set_option autoImplicit false
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {X : Scheme.{u}} {k : Type u} [Field k] {p : X ⟶ Spec (CommRingCat.of k)}
  {U : X.Opens} {m : ℕ}
namespace FunctorialResolution.EmbeddedResolution
namespace EtaleChart
theorem _root_.solution (c : EtaleChart p U m) (hU : IsAffineOpen U)
    (Z : X.IdealSheafData) (S : Finset (Fin m)) (h : restrictIdeal Z U = c.coordIdeal S)
    (i : Fin (m - S.card)) :
    (c.restrictToSubscheme hU Z S h).coord i =
      (Z.subschemeι.appLE U (Z.subschemeι ⁻¹ᵁ U) le_rfl).hom (c.coord (complOrderEmb m S i)) := by
  have hmapeq : (c.restrictToSubscheme hU Z S h).map =
      AffineSpace.homOfVector ((Z.subschemeι ⁻¹ᵁ U).ι ≫ (Z.subschemeι ≫ p))
        (c.restrictToSubschemeCoords Z S) :=
    EtaleChart.ofCoords_map (Z.subschemeι ≫ p) (Z.subschemeι ⁻¹ᵁ U)
      (c.restrictToSubschemeCoords Z S) (c.etale_homOfVector_restrictToSubschemeCoords hU Z S h)
  have hcoord : ((c.restrictToSubscheme hU Z S h).map.appTop).hom
      (AffineSpace.coord (Spec (CommRingCat.of k))
        (ULift.up i : ULift.{u} (Fin (m - S.card))))
      = (Z.subschemeι ⁻¹ᵁ U).topIso.inv.hom
          ((Z.subschemeι.appLE U (Z.subschemeι ⁻¹ᵁ U) le_rfl).hom
            (c.coord (complOrderEmb m S i))) := by
    rw [hmapeq]
    apply AffineSpace.homOfVector_appTop_coord
  rw [EtaleChart.coord_def (c.restrictToSubscheme hU Z S h) i, hcoord]
  exact commRingCatIso_hom_inv_apply _ _
end EtaleChart
end FunctorialResolution.EmbeddedResolution
