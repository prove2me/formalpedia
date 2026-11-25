-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.strictTransform_bot_of_isBlowupAlongIdealSheaf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:59:45.374134+00:00
-- url     : https://prove2.me/submissions/e16f8093-1560-4659-8348-cb8d8c111348

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_OrderReduction_IsomorphismTransport
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_ClosedEmbedding_IsoBlowupPushforward
import Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_ker_preimage___comp_of_isIso_852b3ee68910
import Theorems.Thm_P2M_FunctorialResolution_Blowup_IsLocallyGeneratedByNonZeroDivisor_ker_supportCompl___eq_bot_5a9d7703f0b4
import Theorems.Thm_FunctorialResolution_Blowup_strictTransformImmersion_eq
import Theorems.Thm_FunctorialResolution_Blowup_strictTransformOpens_eq
import Theorems.Thm_FunctorialResolution_Blowup_strictTransform_eq_ker

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
private theorem isIso_subschemeι_comap_bot {X X' : Scheme.{u}} (π : X' ⟶ X) :
    IsIso ((⊥ : X.IdealSheafData).comap π).subschemeι := by
  rw [show (⊥ : X.IdealSheafData).comap π = ⊥ from by simp]
  infer_instance
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {X X' : Scheme.{u}} {π : X' ⟶ X}
    {I : X.IdealSheafData} (h : Blowup.IsBlowupAlongIdealSheaf π I) :
    Blowup.strictTransform π I (⊥ : X.IdealSheafData) = (⊥ : X'.IdealSheafData) := by
  have := isIso_subschemeι_comap_bot π
  rw [Blowup.strictTransform_eq_ker, Blowup.strictTransformImmersion_eq, Blowup.strictTransformOpens_eq]
  exact (ker_preimage_ι_comp_of_isIso _ _).trans h.1.ker_supportCompl_ι_eq_bot
end FunctorialResolution.EmbeddedResolution
