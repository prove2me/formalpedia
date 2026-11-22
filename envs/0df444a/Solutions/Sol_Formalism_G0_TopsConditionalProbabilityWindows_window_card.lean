-- Prove2me | solution 1 for Formalism.G0.TopsConditionalProbabilityWindows.window_card
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:20:45.51701+00:00
-- url     : https://prove2.me/submissions/749b119b-13b4-42a7-802a-8cbae054ba75

import Definitions.Def_Formalism_SubspaceCounting_TopsChoiceSecondBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.G0
open Formalism.G0.TopsConditionalProbabilityWindows
namespace Formalism.G0.TopsConditionalProbabilityWindows
theorem _root_.solution (n i L : ℕ) : (window n i L).card ≤ L := by
  unfold window
  exact card_image_le.trans (card_range L).le
end Formalism.G0.TopsConditionalProbabilityWindows
