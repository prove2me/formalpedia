-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.Data.psi_in_W_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:21:42.949846+00:00
-- url     : https://prove2.me/submissions/0ae0dc52-1287-4192-90f9-37ae1bd5393b

import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_ChainI
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_BaseCaseKOneHolds
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_SecondWayHolds
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_step
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_K_pos
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_noConst_Psi


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries
open Formalism Formalism.BaseCaseIdentities
noncomputable section
open Classical
open Formalism.BaseCaseIdentities.Data
variable {k : Type*} [Field k] {Z C : Type*} [Fintype Z] [Fintype C] (D : Data k Z C)
namespace Formalism.BaseCaseIdentities.Data
theorem _root_.solution : D.PsiW := by
  intro t hnc hW
  refine ⟨D.noConst_Psi t, ?_⟩
  have h := D.step D.K D.K_pos le_rfl t hnc hW
  rwa [min_eq_right (by omega)] at h
end Formalism.BaseCaseIdentities.Data
