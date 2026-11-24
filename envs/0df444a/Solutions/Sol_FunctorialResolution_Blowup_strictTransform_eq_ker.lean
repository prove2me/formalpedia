-- Prove2me | solution 1 for FunctorialResolution.Blowup.strictTransform_eq_ker
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:01:55.653349+00:00
-- url     : https://prove2.me/submissions/f6f4c45e-df36-40d3-88cc-f6de8df95167

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
    strictTransform f Z J = (strictTransformImmersion f Z J).ker := rfl
end FunctorialResolution.Blowup
