-- Prove2me | solution 1 for Formalism.L2.Th1.A.CurveSer.om_coeff_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:33:14.398356+00:00
-- url     : https://prove2.me/submissions/26ad966c-72d5-40d5-9c9b-047d8fcd70cc

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementC
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Theorems.Thm_Formalism_L2_Th1_A_CurveSer_fw_cc
import Theorems.Thm_Formalism_L2_Th1_A_CurveSer_fw_mul_om
import Theorems.Thm_Formalism_L2_Th1_A_CurveSer_om_cc
import Theorems.Thm_Formalism_L2_Th1_A_CurveSer_fw_coeff_one

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
open Formalism.L2.Th1.A.CurveSer
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
namespace Formalism.L2.Th1.A.CurveSer
theorem _root_.solution : coeff 1 (om W) = W.a₁ := by
  have h := congrArg (coeff 1) (fw_mul_om W)
  simp [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
    fw_cc W, om_cc W, fw_coeff_one W, coeff_one] at h
  first
    | linear_combination h
    | linear_combination -h
end Formalism.L2.Th1.A.CurveSer
