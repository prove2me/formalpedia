-- Prove2me | solution 1 for Formalism.L2.Th1.B.Ph.X_mul_lU
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:22:17.313638+00:00
-- url     : https://prove2.me/submissions/53c002a8-95a4-4457-9c3c-85734dcddb48

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_LogSigmaOnePullbackSpec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Ph
open PowerSeries
variable {K : Type} [Field K] [CharZero K]
namespace Formalism.L2.Th1.B.Ph
theorem _root_.solution {l : PowerSeries K} (hl : constantCoeff l = 0) : X * lU l = l := by
  ext n
  rcases n with _ | n
  · rw [coeff_zero_X_mul, coeff_zero_eq_constantCoeff_apply, hl]
  · rw [coeff_succ_X_mul, lU, coeff_mk]
end Formalism.L2.Th1.B.Ph
