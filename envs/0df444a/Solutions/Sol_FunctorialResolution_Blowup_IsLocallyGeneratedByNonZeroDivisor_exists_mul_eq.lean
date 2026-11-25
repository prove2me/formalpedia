-- Prove2me | solution 1 for FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor.exists_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:24:18.454374+00:00
-- url     : https://prove2.me/submissions/d0c4e356-1a74-49b2-b494-aedf6bf6c7a8

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformCharts_ControlledTransform
import Theorems.Thm_FunctorialResolution_Blowup_IsLocallyGeneratedByNonZeroDivisor_mul_idealSheafColon

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
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {Y : Scheme.{u}}
namespace FunctorialResolution.EmbeddedResolution
namespace _root_.FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor
theorem _root_.solution [IsLocallyNoetherian Y]
    {F I' : Y.IdealSheafData} (hF : FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor F) (hI : I' ≤ F) :
    ∃ J : Y.IdealSheafData, F * J = I' :=
  ⟨EmbeddedResolution.idealSheafColon I' F, hF.mul_idealSheafColon hI⟩
end _root_.FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor
end FunctorialResolution.EmbeddedResolution
