-- Prove2me | solution 1 for FunctorialResolution.Blowup.strictTransformOpens_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:01:58.955893+00:00
-- url     : https://prove2.me/submissions/2defdda2-0e96-4351-8ab7-9a9fe341234b

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
theorem _root_.solution {X' X : Scheme.{u}} (f : X' ⟶ X) (Z J : X.IdealSheafData) :
    strictTransformOpens f Z J =
      (J.comap f).subschemeι ⁻¹ᵁ (Z.comap f).support.compl := rfl
end FunctorialResolution.Blowup
