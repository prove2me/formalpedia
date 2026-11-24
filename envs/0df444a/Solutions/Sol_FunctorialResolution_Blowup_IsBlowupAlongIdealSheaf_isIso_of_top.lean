-- Prove2me | solution 1 for FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf.isIso_of_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:00:08.032668+00:00
-- url     : https://prove2.me/submissions/3e9067b5-f8cb-4c85-bcad-e4816dddd981

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Theorems.Thm_FunctorialResolution_Blowup_isLocallyGeneratedByNonZeroDivisor_top
import Theorems.Thm_FunctorialResolution_Blowup_IsBlowupAlongIdealSheaf_isIso_of_isLocallyGeneratedByNonZeroDivisor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry Opposite
open FunctorialResolution FunctorialResolution.Blowup
namespace FunctorialResolution.Blowup
namespace IsBlowupAlongIdealSheaf
theorem _root_.solution {X X' : Scheme.{u}} {π : X' ⟶ X}
    (h : IsBlowupAlongIdealSheaf π (⊤ : X.IdealSheafData)) : IsIso π :=
  h.isIso_of_isLocallyGeneratedByNonZeroDivisor (isLocallyGeneratedByNonZeroDivisor_top X)
end IsBlowupAlongIdealSheaf
end FunctorialResolution.Blowup
