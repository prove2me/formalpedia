-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.existsUnique_pow_mul_eq_comap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:00:19.225782+00:00
-- url     : https://prove2.me/submissions/103cf7c3-f3d8-4a16-937c-0793a262e732

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformCharts_ControlledTransform
import Theorems.Thm_FunctorialResolution_Blowup_IsLocallyGeneratedByNonZeroDivisor_pow
import Theorems.Thm_FunctorialResolution_Blowup_IsLocallyGeneratedByNonZeroDivisor_existsUnique_mul_eq
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_comap_le_exceptionalIdeal_pow

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
variable {X X₁ : Scheme.{u}}
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution [IsLocallyNoetherian X₁] (π : X₁ ⟶ X)
    (Z I : X.IdealSheafData) (n : ℕ) (hZ : Blowup.IsLocallyGeneratedByNonZeroDivisor (Blowup.exceptionalIdeal π Z))
    (hI : I ≤ Z ^ n) :
    ∃! J : X₁.IdealSheafData, Blowup.exceptionalIdeal π Z ^ n * J = I.comap π :=
  (hZ.pow n).existsUnique_mul_eq (comap_le_exceptionalIdeal_pow π hI)
end FunctorialResolution.EmbeddedResolution
