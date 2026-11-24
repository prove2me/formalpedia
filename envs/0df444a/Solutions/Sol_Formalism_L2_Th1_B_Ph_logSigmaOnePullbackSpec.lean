-- Prove2me | solution 1 for Formalism.L2.Th1.B.Ph.logSigmaOnePullbackSpec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:47:59.579926+00:00
-- url     : https://prove2.me/submissions/d44491a3-0d44-4559-a075-1aceda3b997e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_LogSigmaOnePullbackSpec
import Theorems.Thm_Formalism_L2_Th1_B_Ph_hs
import Theorems.Thm_Formalism_L2_Th1_B_Ph_constantCoeff_psubst
import Theorems.Thm_Formalism_L2_Th1_B_Ph_psubst_fExp
import Theorems.Thm_Formalism_L2_Th1_B_Ph_constantCoeff_sig1S
import Theorems.Thm_Formalism_L2_Th1_B_Ph_constantCoeff_gauss
import Theorems.Thm_Formalism_L2_Th1_B_Ph_psubst_gauss
import Theorems.Thm_Formalism_L2_Th1_B_Ph_constantCoeff_phE
import Theorems.Thm_Formalism_L2_Th1_B_fExp_add


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
theorem _root_.solution : PhEDef := by
  intro K _ _ s2 e1 kap w l hl
  refine ⟨constantCoeff_phE s2 e1 kap w hl, ?_⟩
  have hB : constantCoeff (-subst l (sigmaOneSeries e1 kap w)) = 0 := by
    rw [map_neg, constantCoeff_psubst hl, constantCoeff_sig1S, neg_zero]
  have hC : constantCoeff (C (s2 / 2) * l ^ 2) = 0 := by simp [hl]
  have hB' : constantCoeff (subst l (sigmaOneSeries e1 kap w)) = 0 := by
    rw [constantCoeff_psubst hl, constantCoeff_sig1S]
  have hC' : constantCoeff (-(C (s2 / 2) * l ^ 2)) = 0 := constantCoeff_gauss _ hl
  rw [subst_mul (hs hl), sigma1, psubst_fExp hl (constantCoeff_sig1S _ _ _), psubst_gauss _ hl,
    ← fExp_add hB' hC']
  congr 1
  rw [phE]
  ring
end Formalism.L2.Th1.B.Ph
