-- Prove2me | solution 1 for FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf.of_isIso
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:46:01.650062+00:00
-- url     : https://prove2.me/submissions/9a28fedd-bdd3-46d6-a71d-79c5c357928c

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupOpenCover
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeCoproduct
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupCoproduct
import Theorems.Thm_FunctorialResolution_Blowup_isLocallyGeneratedByNonZeroDivisor_comap_top


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open FunctorialResolution FunctorialResolution.Blowup
namespace FunctorialResolution.Blowup
namespace IsBlowupAlongIdealSheaf
theorem _root_.solution {X X' : Scheme.{u}} (f : X' ⟶ X) [IsIso f] :
    IsBlowupAlongIdealSheaf f (⊤ : X.IdealSheafData) := by
  refine And.intro (isLocallyGeneratedByNonZeroDivisor_comap_top f) ?_
  intro W g _
  refine ExistsUnique.intro (g ≫ inv f) ?_ ?_
  · simp
  · intro a ha
    rw [← ha]
    simp
end IsBlowupAlongIdealSheaf
end FunctorialResolution.Blowup
