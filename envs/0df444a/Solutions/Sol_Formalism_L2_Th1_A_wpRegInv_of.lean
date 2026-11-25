-- Prove2me | solution 1 for Formalism.L2.Th1.A.wpRegInv_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:39:55.447681+00:00
-- url     : https://prove2.me/submissions/93896e33-6b15-4b3d-8172-79e620b3026c

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementK
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_BridgeK
import Theorems.Thm_Formalism_L2_Th1_A_BridgeK_cW_succ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
namespace Formalism.L2.Th1.A
theorem _root_.solution (hS : WpShape.{0}) (hR : WpRecursion.{0}) : WpRegInv := by
  unfold WpRegInv
  intro K _ _ W W' h2 h3
  ext n
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [← BridgeK.cW_succ hS hR W k, ← BridgeK.cW_succ hS hR W' k, h2, h3]
  · rw [(hS K W).2.2.1 _ (odd_two_mul_add_one k), (hS K W').2.2.1 _ (odd_two_mul_add_one k)]
end Formalism.L2.Th1.A
