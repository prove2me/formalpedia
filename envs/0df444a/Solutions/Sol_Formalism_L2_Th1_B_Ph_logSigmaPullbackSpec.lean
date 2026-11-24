-- Prove2me | solution 1 for Formalism.L2.Th1.B.Ph.logSigmaPullbackSpec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:48:02.113159+00:00
-- url     : https://prove2.me/submissions/8787574c-d88a-46c5-850a-0a73df06682e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_LogSigmaOnePullbackSpec
import Theorems.Thm_Formalism_L2_Th1_B_Ph_hs
import Theorems.Thm_Formalism_L2_Th1_B_Ph_constantCoeff_psubst
import Theorems.Thm_Formalism_L2_Th1_B_Ph_psubst_fExp
import Theorems.Thm_Formalism_L2_Th1_B_Ph_constantCoeff_sigS
import Theorems.Thm_Formalism_L2_Th1_B_Ph_X_mul_lU
import Theorems.Thm_Formalism_L2_Th1_B_Ph_constantCoeff_lU
import Theorems.Thm_Formalism_L2_Th1_B_Ph_constantCoeff_gauss
import Theorems.Thm_Formalism_L2_Th1_B_Ph_psubst_gauss
import Theorems.Thm_Formalism_L2_Th1_B_Ph_constantCoeff_phO
import Theorems.Thm_Formalism_L2_Th1_B_constantCoeff_fLog
import Theorems.Thm_Formalism_L2_Th1_B_fExp_add
import Theorems.Thm_Formalism_L2_Th1_B_fExp_fLog


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
namespace Formalism.L2.Th1.B.Ph
theorem _root_.solution : PhODef := by
  intro K _ _ s2 P l hl hl1
  refine ⟨constantCoeff_phO s2 P hl hl1, ?_⟩
  have hlu : MvPowerSeries.constantCoeff (lU l) = 1 := by
    have := constantCoeff_lU l
    rw [hl1] at this
    exact this
  have hA : constantCoeff (fLog (lU l)) = 0 := constantCoeff_fLog hlu
  have hB : constantCoeff (subst l (sigS P)) = 0 := by rw [constantCoeff_psubst hl, constantCoeff_sigS]
  have hC : constantCoeff (-(C (s2 / 2) * l ^ 2)) = 0 := constantCoeff_gauss _ hl
  have hAB : constantCoeff (fLog (lU l) + subst l (sigS P)) = 0 := by rw [map_add, hA, hB, add_zero]
  have e : -phO s2 P l = fLog (lU l) + subst l (sigS P) + -(C (s2 / 2) * l ^ 2) := by
    rw [phO]
    ring
  rw [sgStar, sigma, subst_mul (hs hl), subst_mul (hs hl), subst_X (hs hl),
    psubst_fExp hl (constantCoeff_sigS P), psubst_gauss _ hl]
  calc l * fExp (subst l (sigS P)) * fExp (-(C (s2 / 2) * l ^ 2))
      = X * fExp (fLog (lU l)) * fExp (subst l (sigS P)) * fExp (-(C (s2 / 2) * l ^ 2)) := by
        rw [fExp_fLog hlu, X_mul_lU hl]
    _ = X * fExp (-phO s2 P l) := by
        rw [e, fExp_add hAB hC, fExp_add hA hB]
        ring
end Formalism.L2.Th1.B.Ph
