-- Prove2me | solution 1 for Formalism.L2.Th1.B.Fs.eval_last_zero_det_three_points
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:30:31.750806+00:00
-- url     : https://prove2.me/submissions/fe35b889-3e38-4587-86c4-0e5fce286ff9

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_RealAdelicInertTransportTypeFormsEqAlt
import Theorems.Thm_Formalism_L2_Th1_B_Fs_eval_last_zero_X_zero
import Theorems.Thm_Formalism_L2_Th1_B_Fs_eval_last_zero_X_one
import Theorems.Thm_Formalism_L2_Th1_B_Fs_eval_last_zero_X_two
import Theorems.Thm_Formalism_L2_Th1_B_Fs_eval_last_zero_at_variable_zero
import Theorems.Thm_Formalism_L2_Th1_B_Fs_eval_last_zero_at_variable_one
import Theorems.Thm_Formalism_L2_Th1_B_Fs_det_three_points_eq_expansion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Fs
open Formalism.InvariantFactorPaths.G7 (at1)
variable {K : Type} [Field K] [CharZero K]
local notation "A3" => MvPowerSeries (Fin 3) K
namespace Formalism.L2.Th1.B.Fs
theorem _root_.solution (P : PowerSeries K) :
    ev3H (det3 P) = -2 * (MvPowerSeries.X 0 * MvPowerSeries.X 1) * wp3 P 0 1 := by
  rw [det_three_points_eq_expansion]
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_one, map_ofNat, eval_last_zero_X_zero, eval_last_zero_X_one,
    eval_last_zero_X_two, eval_last_zero_at_variable_zero, eval_last_zero_at_variable_one, wp3]
  ring
end Formalism.L2.Th1.B.Fs
