-- Prove2me | solution 1 for FunctorialResolution.Blowup.schemeImageIdeal_eq_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:23:12.283858+00:00
-- url     : https://prove2.me/submissions/37e50f37-7902-406a-9208-a4ad66b300ef

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
theorem _root_.solution {X Y : Scheme.{u}} (f : X ⟶ Y) (I : X.IdealSheafData) :
    schemeImageIdeal f I = (I.subschemeι ≫ f).ker := rfl
end FunctorialResolution.Blowup
