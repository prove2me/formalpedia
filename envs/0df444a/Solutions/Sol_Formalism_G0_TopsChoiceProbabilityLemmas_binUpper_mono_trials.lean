-- Prove2me | solution 1 for Formalism.G0.TopsChoiceProbabilityLemmas.binUpper_mono_trials
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:24:33.516606+00:00
-- url     : https://prove2.me/submissions/e85ca6ca-76ac-4467-ac76-c149399f13e7

import Definitions.Def_Formalism_SubspaceCounting_GoodOrbitIntervalTileCondition
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartA
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_ChoiceOfTopsRefined
import Theorems.Thm_Formalism_G0_TopsChoiceProbabilityLemmas_prob_marginal
import Theorems.Thm_Formalism_G0_TopsChoiceProbabilityLemmas_prob_le_card_eq_binUpper
import Theorems.Thm_Formalism_G0_TopsConditionalProbabilityWindows_P_mono


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
theorem _root_.solution {m G : ℕ} (h : m ≤ G) {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (N : ℕ) :
    binUpper m δ N ≤ binUpper G δ N := by
  have e1 := prob_le_card_eq_binUpper (range m) δ N
  have e2 := prob_le_card_eq_binUpper (range G) δ N
  rw [card_range] at e1 e2
  rw [← e1, ← e2, ← prob_marginal δ (range_subset_range.2 h)]
  apply P_mono h0 h1
  intro t _ hN
  exact hN.trans (card_le_card inter_subset_left)
end Formalism.G0.TopsChoiceProbabilityLemmas
