-- Prove2me | solution 1 for Formalism.L2.Th1.B.Sq.sigmaOneEven
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:14:06.804698+00:00
-- url     : https://prove2.me/submissions/ce7d789a-2f67-4c21-b185-0d39a40c633d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_WeierstrassReducedEquations
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_ConstantCoeffSig1S
import Theorems.Thm_Formalism_L2_Th1_B_Sq_fExp_even
import Theorems.Thm_Formalism_L2_Th1_B_Sq_prim_prim_even
import Theorems.Thm_Formalism_L2_Th1_B_Sq_constantCoeff_sig1S
import Theorems.Thm_Formalism_L2_Th1_B_constantCoeff_fExp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Sq
open PowerSeries
variable {K : Type} [Field K] [CharZero K]
namespace Formalism.L2.Th1.B.Sq
theorem _root_.solution : Sigma1Even := by
  intro K _ _ e1 kap w hw
  have hf : ∀ n, Odd n → coeff n (PowerSeries.C e1 + PowerSeries.C kap * w) = 0 := by
    intro n hn
    have hn0 : n ≠ 0 := hn.pos.ne'
    simp [PowerSeries.coeff_C, hn0, PowerSeries.coeff_C_mul, hw n hn]
  have hs : ∀ n, Odd n → coeff n (sigmaOneSeries e1 kap w) = 0 := by
    intro n hn
    rw [sigmaOneSeries, map_neg, prim_prim_even hf n hn, neg_zero]
  exact ⟨constantCoeff_fExp (constantCoeff_sig1S e1 kap w), fExp_even (constantCoeff_sig1S e1 kap w) hs⟩
end Formalism.L2.Th1.B.Sq
