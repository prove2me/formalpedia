-- Prove2me | solution 1 for Formalism.RankGapBounds.FormsTensorLocalization.localization_reduction_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:32:55.506817+00:00
-- url     : https://prove2.me/submissions/f257cf52-c13d-45d4-ba20-9ce5e704f0cd

import Definitions.Def_Formalism_RankGapBounds_TheoremALocOfLemmaA
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FormsTensorLocalization

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct
open Formalism Formalism.RankGapBounds Formalism.RankGapBounds.FormsTensorLocalization
open Formalism.UG
namespace Formalism.RankGapBounds.FormsTensorLocalization
theorem _root_.solution : LocStep := by
  intro T _ M _ _ S N t e h y
  induction y using LocalizedModule.induction_on with
  | h m s =>
    exact ⟨t ^ e • m, h m, s, (LocalizedModule.smul'_mk _ _ _).symm⟩
end Formalism.RankGapBounds.FormsTensorLocalization
