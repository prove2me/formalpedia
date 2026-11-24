-- Prove2me | solution 1 for Formalism.L2.Th1.B.Ph.phE_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:30:48.053424+00:00
-- url     : https://prove2.me/submissions/7ae2117c-3905-4de6-8519-efd4124566d1

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_LogSigmaOnePullbackSpec
import Theorems.Thm_Formalism_L2_Th1_B_Ph_hs
import Theorems.Thm_Formalism_L2_Th1_B_Ph_psubst_neg
import Theorems.Thm_Formalism_L2_Th1_B_Ph_psubst_C_mul
import Theorems.Thm_Formalism_L2_Th1_B_Ph_psubst_neg_of_even
import Theorems.Thm_Formalism_L2_Th1_B_Ph_sigmaOneLogPart_even

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
theorem _root_.solution (s2 e1 kap : K) {w l i : PowerSeries K} (hw : ∀ n, Odd n → coeff n w = 0)
    (hl : constantCoeff l = 0) (hi : constantCoeff i = 0) (hli : subst i l = -l) :
    subst i (phE s2 e1 kap w l) = phE s2 e1 kap w l := by
  rw [phE, subst_add (hs hi), psubst_neg hi, psubst_C_mul hi, subst_pow (hs hi), hli,
    subst_comp_subst_apply (hs hl) (hs hi), hli, psubst_neg_of_even (sigmaOneLogPart_even e1 kap hw) hl, neg_sq]
end Formalism.L2.Th1.B.Ph
