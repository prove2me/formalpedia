-- Prove2me | solution 1 for Formalism.L2.Th1.A.invariant_differential_units
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:44:17.798826+00:00
-- url     : https://prove2.me/submissions/4001c6f7-f182-4817-891c-e505ae92a51a

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementC
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Theorems.Thm_Formalism_L2_Th1_A_CurveSer_fw_cc
import Theorems.Thm_Formalism_L2_Th1_A_CurveSer_fw_mul_om
import Theorems.Thm_Formalism_L2_Th1_A_CurveSer_om_cc
import Theorems.Thm_Formalism_L2_Th1_A_CurveSer_om_coeff_one
import Theorems.Thm_Formalism_L2_Th1_A_CurveSer_om_coeff_two
import Theorems.Thm_Formalism_L2_Th1_A_CurveSer_iDen_cc
import Theorems.Thm_Formalism_L2_Th1_A_CurveSer_iDen_mul_inv

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
open CurveSer
namespace Formalism.L2.Th1.A
theorem _root_.solution : UnitSpec.{u} := by
  unfold UnitSpec
  intro R _ W
  exact ⟨fw_cc W, fw_mul_om W, om_cc W, om_coeff_one W, om_coeff_two W, iDen_cc W, iDen_mul_inv W⟩
end Formalism.L2.Th1.A
