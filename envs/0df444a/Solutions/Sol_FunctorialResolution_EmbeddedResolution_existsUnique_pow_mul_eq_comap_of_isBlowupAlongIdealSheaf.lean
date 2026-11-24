-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.existsUnique_pow_mul_eq_comap_of_isBlowupAlongIdealSheaf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:14:35.84632+00:00
-- url     : https://prove2.me/submissions/3997bce9-7b4f-4dce-afe2-110194229196

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformCharts_ControlledTransform
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_existsUnique_pow_mul_eq_comap
import Theorems.Thm_FunctorialResolution_Blowup_exceptionalIdeal_eq_comap


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
    (Z I : X.IdealSheafData) (n : ℕ) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (hI : I ≤ Z ^ n) :
    ∃! J : X₁.IdealSheafData, Blowup.exceptionalIdeal π Z ^ n * J = I.comap π := by
  have hZ : Blowup.IsLocallyGeneratedByNonZeroDivisor (Blowup.exceptionalIdeal π Z) := by
    rw [Blowup.exceptionalIdeal_eq_comap]
    exact hπ.1
  exact existsUnique_pow_mul_eq_comap π Z I n hZ hI
end FunctorialResolution.EmbeddedResolution
