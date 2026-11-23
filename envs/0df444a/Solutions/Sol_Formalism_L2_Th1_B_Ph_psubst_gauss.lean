-- Prove2me | solution 1 for Formalism.L2.Th1.B.Ph.psubst_gauss
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:22:29.885887+00:00
-- url     : https://prove2.me/submissions/c897ee31-e483-40e3-b2c6-c38425a85a4a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_LogSigmaOnePullbackSpec
import Theorems.Thm_Formalism_L2_Th1_B_Ph_hs
import Theorems.Thm_Formalism_L2_Th1_B_Ph_psubst_neg
import Theorems.Thm_Formalism_L2_Th1_B_Ph_psubst_C_mul
import Theorems.Thm_Formalism_L2_Th1_B_Ph_psubst_fExp

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
theorem _root_.solution (c : K) {l : PowerSeries K} (hl : constantCoeff l = 0) :
    subst l (fExp (-(C c * X ^ 2))) = fExp (-(C c * l ^ 2)) := by
  rw [psubst_fExp hl (by simp), psubst_neg hl, psubst_C_mul hl, subst_pow (hs hl), subst_X (hs hl)]
end Formalism.L2.Th1.B.Ph
