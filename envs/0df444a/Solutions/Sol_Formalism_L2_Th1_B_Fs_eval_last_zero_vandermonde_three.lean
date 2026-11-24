-- Prove2me | solution 1 for Formalism.L2.Th1.B.Fs.eval_last_zero_vandermonde_three
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:13:15.156011+00:00
-- url     : https://prove2.me/submissions/d65198ab-db29-4cef-ab27-3cf3b1aa9b53

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_RealAdelicInertTransportTypeFormsEqAlt
import Theorems.Thm_Formalism_L2_Th1_B_Fs_eval_last_zero_X_zero
import Theorems.Thm_Formalism_L2_Th1_B_Fs_eval_last_zero_X_one
import Theorems.Thm_Formalism_L2_Th1_B_Fs_eval_last_zero_X_two

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
theorem _root_.solution : ev3H (vand3 K) =
    (MvPowerSeries.X 0 * MvPowerSeries.X 1) * (MvPowerSeries.X 0 ^ 2 - MvPowerSeries.X 1 ^ 2) := by
  simp only [vand3, map_add, map_sub, map_mul, eval_last_zero_X_zero, eval_last_zero_X_one, eval_last_zero_X_two]
  ring
end Formalism.L2.Th1.B.Fs
