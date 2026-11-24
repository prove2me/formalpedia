-- Prove2me | solution 1 for Formalism.L2.Th1.B.Det.determinant_derivative_rule_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:43:39.011803+00:00
-- url     : https://prove2.me/submissions/b583b478-84bc-436f-8ceb-33b65c972a3c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_Wp3ApplyEqSqMulSubSqMul
import Theorems.Thm_Formalism_L2_Th1_B_Det_X_ne
import Theorems.Thm_Formalism_L2_Th1_B_Det_wp3_apply_eq_sq_mul_sub_sq_mul
import Theorems.Thm_Formalism_L2_Th1_B_Det_det_three_points_eq_expansion
import Theorems.Thm_Formalism_L2_Th1_B_Det_X_mul_dXt
import Theorems.Thm_Formalism_L2_Th1_B_Det_curve_eq
import Theorems.Thm_Formalism_L2_Th1_B_Det_X_mul_dYt
import Theorems.Thm_Formalism_L2_Th1_B_Det_pderiv_left_weierstrass_pair
import Theorems.Thm_Formalism_L2_Th1_B_Det_pderiv_right_weierstrass_pair
import Theorems.Thm_Formalism_L2_Th1_B_Det_pderiv_one_det_three_points
import Theorems.Thm_Formalism_L2_Th1_B_Det_pderiv_two_det_three_points
import Theorems.Thm_Formalism_L2_Th1_B_Det_core2
import Theorems.Thm_Formalism_L2_Th1_B_X_ne


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Det
open Formalism.InvariantFactorPaths.G7 (at1)
namespace Formalism.L2.Th1.B.Det
theorem _root_.solution : DetRule := by
  intro K _ _ g2 g3 P hP
  have key := core2 (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K) (MvPowerSeries.X 1) (MvPowerSeries.X 2) (Xt P 0) (Yt P 0)
    (Xt P 1) (Yt P 1) (Xt P 2) (Yt P 2) (MvPowerSeries.C (g2 / 2)) (MvPowerSeries.C g3)
    (dXt P 0) (dXt P 1) (dXt P 2) (dYt P 1) (dYt P 2) (curve_eq hP 0) (curve_eq hP 1)
    (curve_eq hP 2) (X_mul_dXt P 0) (X_mul_dXt P 1) (X_mul_dXt P 2) (X_mul_dYt hP 1)
    (X_mul_dYt hP 2)
  have habc : (MvPowerSeries.X 0 * MvPowerSeries.X 1 * MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (X_ne 0) (X_ne 1)) (X_ne 2)
  rw [pderiv_one_det_three_points, pderiv_two_det_three_points, pderiv_left_weierstrass_pair P (by decide : (1 : Fin 3) ≠ 0),
    pderiv_right_weierstrass_pair P (by decide : (0 : Fin 3) ≠ 1), pderiv_left_weierstrass_pair P (by decide : (2 : Fin 3) ≠ 0),
    pderiv_right_weierstrass_pair P (by decide : (0 : Fin 3) ≠ 2), pderiv_left_weierstrass_pair P (by decide : (2 : Fin 3) ≠ 1),
    pderiv_right_weierstrass_pair P (by decide : (1 : Fin 3) ≠ 2), wp3_apply_eq_sq_mul_sub_sq_mul, wp3_apply_eq_sq_mul_sub_sq_mul, wp3_apply_eq_sq_mul_sub_sq_mul, det_three_points_eq_expansion]
  apply mul_left_cancel₀ habc
  linear_combination key
end Formalism.L2.Th1.B.Det
