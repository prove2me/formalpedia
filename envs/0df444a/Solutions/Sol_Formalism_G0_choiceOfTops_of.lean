-- Prove2me | solution 1 for Formalism.G0.choiceOfTops_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:19:37.426802+00:00
-- url     : https://prove2.me/submissions/4e900ab1-46d8-4355-9fe5-703eb886d6cb

import Definitions.Def_Formalism_SubspaceCounting_TopsChoiceSecondBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_ChoiceOfTops
import Theorems.Thm_Formalism_G0_ChoiceOfTopsP_probNotGood_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.G0
namespace Formalism.G0
theorem _root_.solution (ha : TopsChoicePartA) (hb : TopsChoiceSecondBound) (hc : TopsChoiceThirdBound) (hn : SmallCardCondProbBound) : ChoiceOfTops := by
  intro n δ L₂ K r N₁ G hn2 hev hδ hL hLδ hr hN
  have hL' : (1 : ℝ) ≤ L₂ := by exact_mod_cast hL
  have hδ1 : δ ≤ 1 := by nlinarith
  have h := ChoiceOfTopsP.probNotGood_le n δ L₂ K r N₁ G hδ hδ1
  have h1 := ha n δ L₂ K hn2 hδ hL hLδ
  have h2 := hb n δ L₂ r N₁ hn2 hev hδ hL hLδ hr hN
  have h3 := hc n δ G hn2 hδ hδ1
  have h4 := hn n δ N₁ hn2 hδ hδ1
  linarith
end Formalism.G0
