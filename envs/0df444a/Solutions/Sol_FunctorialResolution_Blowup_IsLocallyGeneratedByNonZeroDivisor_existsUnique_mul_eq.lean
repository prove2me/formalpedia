-- Prove2me | solution 1 for FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor.existsUnique_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:46:37.878652+00:00
-- url     : https://prove2.me/submissions/e7bc6b9f-a3a1-4056-9d16-851e208cca1e

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformCharts_ControlledTransform
import Theorems.Thm_FunctorialResolution_Blowup_IsLocallyGeneratedByNonZeroDivisor_eq_of_mul_eq_mul
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
    ∃! J : Y.IdealSheafData, F * J = I' := by
  refine ⟨EmbeddedResolution.idealSheafColon I' F, hF.mul_idealSheafColon hI, ?_⟩
  intro J hJ
  exact hF.eq_of_mul_eq_mul (hJ.trans (hF.mul_idealSheafColon hI).symm)
end _root_.FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor
end FunctorialResolution.EmbeddedResolution
