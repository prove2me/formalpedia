-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.eq_controlledTransform_of_mul_eq_comap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:30:04.45065+00:00
-- url     : https://prove2.me/submissions/16bdc605-a85f-4a9e-b0ad-0ddbb0333302

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformCharts_ControlledTransform
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_existsUnique_pow_mul_eq_comap_of_isBlowupAlongIdealSheaf
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_exceptionalIdeal_pow_mul_controlledTransform

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
    (Z I : X.IdealSheafData) (n : ℕ) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (hI : I ≤ Z ^ n)
    (J : X₁.IdealSheafData) (hJ : Blowup.exceptionalIdeal π Z ^ n * J = I.comap π) :
    J = controlledTransform π Z I n hπ hI :=
  (existsUnique_pow_mul_eq_comap_of_isBlowupAlongIdealSheaf π Z I n hπ hI).unique hJ
    (exceptionalIdeal_pow_mul_controlledTransform π Z I n hπ hI)
end FunctorialResolution.EmbeddedResolution
