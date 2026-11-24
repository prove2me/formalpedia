-- Prove2me | solution 1 for FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor.eq_of_mul_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:44:19.491887+00:00
-- url     : https://prove2.me/submissions/d0e12fc4-270e-4838-9b23-2f728fdadfb5

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformCharts_ControlledTransform
import Theorems.Thm_FunctorialResolution_Blowup_IsLocallyGeneratedByNonZeroDivisor_le_of_mul_le_mul

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
theorem _root_.solution {F J J' : Y.IdealSheafData}
    (hF : FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor F) (h : F * J = F * J') : J = J' :=
  le_antisymm (hF.le_of_mul_le_mul (le_of_eq h)) (hF.le_of_mul_le_mul (le_of_eq h.symm))
end _root_.FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor
end FunctorialResolution.EmbeddedResolution
