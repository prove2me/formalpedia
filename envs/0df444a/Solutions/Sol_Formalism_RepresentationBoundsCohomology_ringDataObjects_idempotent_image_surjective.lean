-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.ringDataObjects.idempotent_image_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:41:58.98767+00:00
-- url     : https://prove2.me/submissions/24f4cfbf-f10a-443a-9312-3f60d03fbe55

import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RightIdealImageOfSurjective
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_GlobalModuleOf
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_IdempotentImageSurjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.RepresentationBoundsCohomology Formalism.RepresentationBoundsCohomology.ringDataObjects
open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities
namespace Formalism.RepresentationBoundsCohomology.ringDataObjects
theorem _root_.solution : RightIdealImageOfSurjective := by
  unfold RightIdealImageOfSurjective
  intro O R' _ _ _ n _ _ ρ hρ e₁ A
  constructor
  · rintro ⟨B, rfl⟩
    obtain ⟨b, rfl⟩ := hρ B
    exact ⟨b, by rw [map_mul]⟩
  · rintro ⟨a, rfl⟩
    exact ⟨ρ a, by rw [map_mul]⟩
end Formalism.RepresentationBoundsCohomology.ringDataObjects
