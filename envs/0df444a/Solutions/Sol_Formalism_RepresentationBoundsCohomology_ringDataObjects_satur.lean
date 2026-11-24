-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.ringDataObjects.satur
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:36:48.191068+00:00
-- url     : https://prove2.me/submissions/dadde300-8f72-4f75-8790-c7a973ba4f3b

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
theorem _root_.solution : DvrArtinReesInclusion := by
  unfold DvrArtinReesInclusion
  intro O _ _ _ M _ _ _ _ R
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul (IsLocalRing.maximalIdeal O) R
  refine ⟨k + 1, fun a ha haN => ?_⟩
  have hmem : a ∈ (IsLocalRing.maximalIdeal O) ^ (k + 1) • (⊤ : Submodule O M) ⊓ R :=
    Submodule.mem_inf.2 ⟨haN, ha⟩
  rw [hk (k + 1) (Nat.le_succ k), Nat.add_sub_cancel_left, pow_one] at hmem
  exact Submodule.smul_mono le_rfl inf_le_right hmem
end Formalism.RepresentationBoundsCohomology.ringDataObjects
