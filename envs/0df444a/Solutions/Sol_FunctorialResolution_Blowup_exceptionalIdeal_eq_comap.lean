-- Prove2me | solution 1 for FunctorialResolution.Blowup.exceptionalIdeal_eq_comap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:01:55.61916+00:00
-- url     : https://prove2.me/submissions/fe5e3a9f-a4ba-4bf0-9e18-65479717d000

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open FunctorialResolution FunctorialResolution.Blowup
noncomputable section
namespace FunctorialResolution.Blowup
theorem _root_.solution {X' X : Scheme.{u}} (f : X' ⟶ X) (Z : X.IdealSheafData) :
    exceptionalIdeal f Z = Z.comap f := rfl
end FunctorialResolution.Blowup
