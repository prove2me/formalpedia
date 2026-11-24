-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.restrictIdeal_eq_of_le_of_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:50:08.050244+00:00
-- url     : https://prove2.me/submissions/8425a608-a146-466b-942b-8d0289a70d6d

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_restrictIdeal_eq_comap_homOfLE_restrictIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {X : Scheme.{u}} {I J : X.IdealSheafData} {U V : X.Opens}
    (h : V ≤ U) (hU : restrictIdeal I U = restrictIdeal J U) :
    restrictIdeal I V = restrictIdeal J V := by
  rw [restrictIdeal_eq_comap_homOfLE_restrictIdeal I h,
    restrictIdeal_eq_comap_homOfLE_restrictIdeal J h, hU]
end FunctorialResolution.EmbeddedResolution
