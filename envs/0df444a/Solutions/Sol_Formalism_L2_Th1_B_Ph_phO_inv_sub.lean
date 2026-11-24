-- Prove2me | solution 1 for Formalism.L2.Th1.B.Ph.phO_inv_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:33:38.071909+00:00
-- url     : https://prove2.me/submissions/88b62d8d-21ac-4e7b-aa2c-3a8a0842d96d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_LogSigmaOnePullbackSpec
import Theorems.Thm_Formalism_L2_Th1_B_Ph_hs
import Theorems.Thm_Formalism_L2_Th1_B_Ph_psubst_neg
import Theorems.Thm_Formalism_L2_Th1_B_Ph_psubst_C_mul
import Theorems.Thm_Formalism_L2_Th1_B_Ph_psubst_fLog
import Theorems.Thm_Formalism_L2_Th1_B_Ph_psubst_neg_of_even
import Theorems.Thm_Formalism_L2_Th1_B_Ph_sigS_even
import Theorems.Thm_Formalism_L2_Th1_B_Ph_constantCoeff_lU

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
theorem _root_.solution (s2 : K) {P l i : PowerSeries K} (hP : ∀ n, Odd n → coeff n P = 0)
    (hl : constantCoeff l = 0) (hl1 : coeff 1 l = 1) (hi : constantCoeff i = 0)
    (hli : subst i l = -l) :
    subst i (phO s2 P l) - phO s2 P l = fLog (lU l) - fLog (subst i (lU l)) := by
  have hlu : MvPowerSeries.constantCoeff (lU l) = 1 := by
    have := constantCoeff_lU l
    rw [hl1] at this
    exact this
  rw [phO, subst_sub (hs hi), subst_add (hs hi), psubst_neg hi, psubst_C_mul hi, subst_pow (hs hi),
    hli, subst_comp_subst_apply (hs hl) (hs hi), hli, psubst_neg_of_even (sigS_even hP) hl,
    psubst_fLog hi hlu, neg_sq]
  ring
end Formalism.L2.Th1.B.Ph
