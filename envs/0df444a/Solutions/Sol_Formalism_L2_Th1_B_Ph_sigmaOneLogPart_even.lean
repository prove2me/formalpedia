-- Prove2me | solution 1 for Formalism.L2.Th1.B.Ph.sigmaOneLogPart_even
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:20:52.783987+00:00
-- url     : https://prove2.me/submissions/835ec144-63a0-48a5-9394-e638d674cb38

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_LogSigmaOnePullbackSpec
import Theorems.Thm_Formalism_L2_Th1_B_Ph_prim_prim_even

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
theorem _root_.solution (e1 kap : K) {w : PowerSeries K} (hw : ∀ n, Odd n → coeff n w = 0) :
    ∀ n, Odd n → coeff n (sigmaOneSeries e1 kap w) = 0 := by
  intro n hn
  have hev : ∀ m, Odd m → coeff m (C e1 + C kap * w) = 0 := by
    intro m hm
    simp [coeff_C, coeff_C_mul, hw m hm, hm.pos.ne']
  rw [sigmaOneSeries, map_neg, prim_prim_even hev n hn, neg_zero]
end Formalism.L2.Th1.B.Ph
