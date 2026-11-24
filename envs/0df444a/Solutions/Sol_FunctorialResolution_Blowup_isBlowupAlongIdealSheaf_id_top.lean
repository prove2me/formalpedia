-- Prove2me | solution 1 for FunctorialResolution.Blowup.isBlowupAlongIdealSheaf_id_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:46:27.390852+00:00
-- url     : https://prove2.me/submissions/f2f27d19-2674-4fb6-9037-08f623b4b386

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupOpenCover
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeCoproduct
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupCoproduct
import Theorems.Thm_FunctorialResolution_Blowup_IsBlowupAlongIdealSheaf_of_isIso

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
theorem _root_.solution (X : Scheme.{u}) : IsBlowupAlongIdealSheaf (𝟙 X) (⊤ : X.IdealSheafData) :=
  IsBlowupAlongIdealSheaf.of_isIso (𝟙 X)
end FunctorialResolution.Blowup
