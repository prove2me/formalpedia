-- Prove2me | solution 1 for Formalism.WeaklyAdmissibleFiltrations.rankOneWA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:54:09.353428+00:00
-- url     : https://prove2.me/submissions/6c8433a8-8bdd-4442-b646-b0ac800f9731

import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CocyclesFunctorial
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_RankOne
import Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_FilPhi_rankOne_isSub_bot_or_top
import Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_FilPhi_rankOne_tH_bot
import Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_FilPhi_rankOne_det_bot
import Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_FilPhi_rankOne_det_top

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.WeaklyAdmissibleFiltrations
open Module
namespace Formalism.WeaklyAdmissibleFiltrations
theorem _root_.solution : RankOneWA := by
  intro LL _ D _ _ _ n _ Emb _ F v hl
  constructor
  · exact fun h => h.1
  · intro htop
    refine ⟨htop, fun D' h => ?_⟩
    rcases F.rankOne_isSub_bot_or_top hl D' h with rfl | rfl
    · unfold FilPhi.NewtonAbove
      rw [F.rankOne_tH_bot, F.rankOne_det_bot, AddValuation.map_one]
      simp
    · unfold FilPhi.NewtonAbove
      rw [F.rankOne_det_top]
      exact le_of_eq htop
end Formalism.WeaklyAdmissibleFiltrations
