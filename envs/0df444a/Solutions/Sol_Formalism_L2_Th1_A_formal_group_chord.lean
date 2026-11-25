-- Prove2me | solution 1 for Formalism.L2.Th1.A.formal_group_chord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:18:46.264805+00:00
-- url     : https://prove2.me/submissions/f5227fbb-6d90-4bc7-88a8-33f72d4624da

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementG
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsNoTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalGroupEqWSeries
import Theorems.Thm_Formalism_L2_Th1_A_Fgl1_lam_mul
import Theorems.Thm_Formalism_L2_Th1_A_Fgl1_uThird_cc
import Theorems.Thm_Formalism_L2_Th1_A_Fgl1_fgl_cc
import Theorems.Thm_Formalism_L2_Th1_A_Fgl1_fgl_L
import Theorems.Thm_Formalism_L2_Th1_A_Fgl1_wThird_eq
import Theorems.Thm_Formalism_L2_Th1_A_Fgl1_fgl_eq
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_lam_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u v
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
namespace Formalism.L2.Th1.A
theorem _root_.solution : FglChord.{u} := by
  intro R _ W
  refine ⟨?_, Fgl1.uThird_cc W, Fgl1.wThird_eq W, Fgl1.fgl_eq W, Fgl1.fgl_cc W, Fgl1.fgl_L W 0, Fgl1.fgl_L W 1⟩
  rw [mul_comm]
  exact Fgl1.lam_mul W
end Formalism.L2.Th1.A
