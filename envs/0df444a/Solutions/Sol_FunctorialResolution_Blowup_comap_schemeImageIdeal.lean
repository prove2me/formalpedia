-- Prove2me | solution 1 for FunctorialResolution.Blowup.comap_schemeImageIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:46:38.514009+00:00
-- url     : https://prove2.me/submissions/d0aaa2ca-1a34-41c3-8b97-22f4b4d47291

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Theorems.Thm_P2M_FunctorialResolution_Blowup_comap_ker_subscheme__comp_0b937eab6fcc

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
theorem _root_.solution {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
    (I : X.IdealSheafData) : (schemeImageIdeal f I).comap f = I :=
  comap_ker_subschemeι_comp f I
end FunctorialResolution.Blowup
