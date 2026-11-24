-- Prove2me | solution 1 for Formalism.L2.Th1.B.Ph.constantCoeff_phE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:21:20.043107+00:00
-- url     : https://prove2.me/submissions/ad6aa069-7963-4baa-a383-8ba8103fe0c2

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_LogSigmaOnePullbackSpec
import Theorems.Thm_Formalism_L2_Th1_B_Ph_constantCoeff_psubst
import Theorems.Thm_Formalism_L2_Th1_B_Ph_constantCoeff_sig1S

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
theorem _root_.solution (s2 e1 kap : K) (w : PowerSeries K) {l : PowerSeries K}
    (hl : constantCoeff l = 0) : constantCoeff (phE s2 e1 kap w l) = 0 := by
  rw [phE, map_add, map_neg, constantCoeff_psubst hl, constantCoeff_sig1S, map_mul, map_pow, hl]
  simp
end Formalism.L2.Th1.B.Ph
