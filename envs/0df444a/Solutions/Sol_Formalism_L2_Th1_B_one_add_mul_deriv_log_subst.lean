-- Prove2me | solution 1 for Formalism.L2.Th1.B.one_add_mul_deriv_log_subst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:27:56.756508+00:00
-- url     : https://prove2.me/submissions/f33d9481-0955-40f7-b843-17ca92f2afef

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Theorems.Thm_Formalism_L2_Th1_B_one_add_X_mul_deriv_log
import Theorems.Thm_Formalism_L2_Th1_B_one_add_X_subst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B
open PowerSeries
variable {K : Type} [Field K] [CharZero K]
namespace Formalism.L2.Th1.B
theorem _root_.solution {ι : Type} {a : MvPowerSeries ι K} (ha : HasSubst a) :
    (1 + a) * (derivative K (log K)).subst a = 1 := by
  have h := congrArg (PowerSeries.substAlgHom ha) (one_add_X_mul_deriv_log (K := K))
  rw [map_mul, map_one, coe_substAlgHom, one_add_X_subst ha] at h
  exact h
end Formalism.L2.Th1.B
