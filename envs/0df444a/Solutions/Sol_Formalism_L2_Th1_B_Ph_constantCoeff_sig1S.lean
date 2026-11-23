-- Prove2me | solution 1 for Formalism.L2.Th1.B.Ph.constantCoeff_sig1S
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:22:18.05959+00:00
-- url     : https://prove2.me/submissions/18e9d85d-0ca4-4ffc-aeab-78a1d6c63707

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_LogSigmaOnePullbackSpec
import Theorems.Thm_Formalism_L2_Th1_B_Ph_coeff_zero_prim

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
theorem _root_.solution (e1 kap : K) (w : PowerSeries K) :
    constantCoeff (sigmaOneSeries e1 kap w) = 0 := by
  rw [sigmaOneSeries, map_neg, ← coeff_zero_eq_constantCoeff_apply, coeff_zero_prim, neg_zero]
end Formalism.L2.Th1.B.Ph
