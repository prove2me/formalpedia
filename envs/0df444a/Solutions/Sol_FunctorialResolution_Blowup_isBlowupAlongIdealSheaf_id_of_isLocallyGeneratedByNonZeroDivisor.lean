-- Prove2me | solution 1 for FunctorialResolution.Blowup.isBlowupAlongIdealSheaf_id_of_isLocallyGeneratedByNonZeroDivisor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:23:03.453608+00:00
-- url     : https://prove2.me/submissions/3c43fd96-c1cf-4d24-be34-633bd4771ea3

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic

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
theorem _root_.solution {X : Scheme.{u}} (I : X.IdealSheafData)
    (hI : IsLocallyGeneratedByNonZeroDivisor I) : IsBlowupAlongIdealSheaf (𝟙 X) I := by
  constructor
  · rwa [Scheme.IdealSheafData.comap_id]
  · intro W g _
    refine ⟨g, Category.comp_id g, ?_⟩
    intro y hy
    rw [← hy, Category.comp_id]
end FunctorialResolution.Blowup
