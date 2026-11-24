-- Prove2me | solution 1 for Formalism.L2.Th1.B.Fs.eval_last_zero_at_variable_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:20:20.21643+00:00
-- url     : https://prove2.me/submissions/857e5c45-7c90-4f67-bf72-e0b9a805572f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_RealAdelicInertTransportTypeFormsEqAlt
import Theorems.Thm_Formalism_L2_Th1_B_Fs_eval_last_zero_X_zero
import Theorems.Thm_Formalism_L2_Th1_B_Fs_eval_last_zero_subst_series

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
theorem _root_.solution (f : PowerSeries K) : ev3H (at1 0 f) = at1 0 f := by
  rw [at1, eval_last_zero_subst_series f (by simp), eval_last_zero_X_zero]
end Formalism.L2.Th1.B.Fs
