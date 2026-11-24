-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.subschemeMapOfComap_base
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:19:45.658159+00:00
-- url     : https://prove2.me/submissions/7dec0562-ff1e-4c17-9c62-965ed72148ce

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_IdealSheafOpenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_SubschemeMapFlatness
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_ofCoords_map
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coe_complOpensOfIsClosed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleChart.ofCoords_map
attribute [local simp] FunctorialResolution.EmbeddedResolution.coe_complOpensOfIsClosed



set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {X Y : Scheme.{u}} (g : Y ⟶ X) (Z : X.IdealSheafData)
    (y : (Z.comap g).subscheme) :
    Z.subschemeι.base ((subschemeMapOfComap g Z).base y) =
      g.base ((Z.comap g).subschemeι.base y) := by
  have h := subschemeMapOfComap_comp g Z
  have h2 : (subschemeMapOfComap g Z ≫ Z.subschemeι).base y
      = ((Z.comap g).subschemeι ≫ g).base y := by rw [h]
  simpa using h2
end FunctorialResolution.EmbeddedResolution
