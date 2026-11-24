-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.generalizing_subschemeMapOfComap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:49:05.596442+00:00
-- url     : https://prove2.me/submissions/9721e1d3-2d75-49ad-be74-b911d1e7ae75

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_IdealSheafOpenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_SubschemeMapFlatness

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {X Y : Scheme.{u}} (g : Y ⟶ X)
    [AlgebraicGeometry.Flat g] (Z : X.IdealSheafData)
    (y : (Z.comap g).subscheme) (x : Z.subscheme)
    (hx : x ⤳ (subschemeMapOfComap g Z).base y) :
    ∃ y' : (Z.comap g).subscheme, y' ⤳ y ∧ (subschemeMapOfComap g Z).base y' = x := by
  exact AlgebraicGeometry.Flat.generalizingMap (subschemeMapOfComap g Z) hx
end FunctorialResolution.EmbeddedResolution
