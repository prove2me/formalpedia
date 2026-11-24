-- Prove2me | solution 1 for Formalism.G0.TopsChoiceProbabilityLemmas.marked_inter
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:11:58.105143+00:00
-- url     : https://prove2.me/submissions/0382bd41-ed7e-4485-872e-237e383d5a45

import Definitions.Def_Formalism_SubspaceCounting_GoodOrbitIntervalTileCondition
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartA
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_ChoiceOfTopsRefined
import Theorems.Thm_Formalism_G0_TopsChoiceProbabilityLemmas_cell_sub_tile

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
open Formalism.G0.TopsChoiceProbabilityLemmas
open TopsConditionalProbabilityWindows
namespace Formalism.G0.TopsChoiceProbabilityLemmas
theorem _root_.solution (t : Finset ℕ) (r u s : ℕ) :
    Marked t r u s ↔ Marked (t ∩ tile r u s) r u s := by
  unfold Marked
  apply forall_congr'
  intro c
  apply imp_congr_right
  intro hc
  apply imp_congr_right
  intro hc'
  rw [inter_assoc, inter_eq_right.2 (cell_sub_tile hc hc')]
end Formalism.G0.TopsChoiceProbabilityLemmas
