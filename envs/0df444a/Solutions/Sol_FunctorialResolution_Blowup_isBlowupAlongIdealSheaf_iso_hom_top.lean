-- Prove2me | solution 1 for FunctorialResolution.Blowup.isBlowupAlongIdealSheaf_iso_hom_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:33:59.205896+00:00
-- url     : https://prove2.me/submissions/360f1446-00c6-4e1a-a5d0-634f304c31fc

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
theorem _root_.solution {X X' : Scheme.{u}} (e : X' ≅ X) :
    IsBlowupAlongIdealSheaf e.hom (⊤ : X.IdealSheafData) :=
  IsBlowupAlongIdealSheaf.of_isIso e.hom
end FunctorialResolution.Blowup
