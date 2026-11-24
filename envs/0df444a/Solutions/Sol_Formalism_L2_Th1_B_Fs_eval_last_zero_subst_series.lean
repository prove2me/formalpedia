-- Prove2me | solution 1 for Formalism.L2.Th1.B.Fs.eval_last_zero_subst_series
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:10:32.783975+00:00
-- url     : https://prove2.me/submissions/a6e53f93-0f69-4c45-b731-62d21a57695f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_RealAdelicInertTransportTypeFormsEqAlt
import Theorems.Thm_Formalism_L2_Th1_B_Fs_eval_three_eq_eval_last_zero
import Theorems.Thm_Formalism_L2_Th1_B_psubst_msubst


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
theorem _root_.solution (f : PowerSeries K) {u : A3} (hu : MvPowerSeries.constantCoeff u = 0) :
    ev3H (PowerSeries.subst u f) = PowerSeries.subst (ev3H u) f := by
  rw [← eval_three_eq_eval_last_zero, ← eval_three_eq_eval_last_zero, ev3, ev3, psubst_msubst f hu hasSubst_eval_last_zero]
end Formalism.L2.Th1.B.Fs
