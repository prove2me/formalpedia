-- Prove2me | solution 1 for FunctorialResolution.Blowup.blowupIsIsoOffCenter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:14:31.981986+00:00
-- url     : https://prove2.me/submissions/64ab78c8-de4a-43fe-93de-4c44b58a5ecb

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupCoproduct
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupOpenCover
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupIsoOffCenter
import Theorems.Thm_P2M_FunctorialResolution_Blowup_comap___support_compl_eq_top_7d133a646fc9
import Theorems.Thm_FunctorialResolution_Blowup_IsBlowupAlongIdealSheaf_isIso_of_top
import Theorems.Thm_FunctorialResolution_Blowup_IsBlowupAlongIdealSheaf_restrict


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
open FunctorialResolution FunctorialResolution.Blowup
namespace FunctorialResolution.Blowup
theorem _root_.solution : BlowupIsIsoOffCenter.{u} := by
  intro X X' π Z h
  have h1 := h.restrict Z.support.compl
  rw [comap_ι_support_compl_eq_top Z] at h1
  exact h1.isIso_of_top
end FunctorialResolution.Blowup
