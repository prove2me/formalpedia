-- Prove2me | solution 1 for Formalism.L2.Th1.A.WpSh.alg_first
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:20:09.860326+00:00
-- url     : https://prove2.me/submissions/23667d3e-f1a5-4a42-bc7e-0462513c8f22

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementI
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_Laurent
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_WpShape
import Theorems.Thm_Formalism_L2_Th1_A_dLDR_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLD_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.L2.Th1.A.dLDR_apply
attribute [local simp] Formalism.L2.Th1.A.dLD_apply



set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.WpSh
namespace Formalism.L2.Th1.A.WpSh
theorem _root_.solution {S : Type*} [CommRing S] (z zi A B c2 c3 : S) (hz : z * zi = 1)
    (h : (zi ^ 2 * B + (-2) * zi ^ 3 * A) ^ 2 = 4 * (zi ^ 2 * A) ^ 3 - c2 * (zi ^ 2 * A) - c3) :
    (z * B - 2 * A) ^ 2 = 4 * A ^ 3 - c2 * z ^ 4 * A - c3 * z ^ 6 := by
  have e1 : z ^ 6 * (zi ^ 2 * B + (-2) * zi ^ 3 * A) ^ 2 = (z * B * (z * zi) ^ 2 - 2 * A * (z * zi) ^ 3) ^ 2 := by ring
  have e2 : z ^ 6 * (4 * (zi ^ 2 * A) ^ 3 - c2 * (zi ^ 2 * A) - c3)
      = 4 * A ^ 3 * (z * zi) ^ 6 - c2 * z ^ 4 * A * (z * zi) ^ 2 - c3 * z ^ 6 := by ring
  rw [hz] at e1 e2
  simp only [one_pow, mul_one] at e1 e2
  rw [← e1, h, e2]
end Formalism.L2.Th1.A.WpSh
