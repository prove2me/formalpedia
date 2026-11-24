-- Prove2me | solution 1 for Formalism.L2.Th1.B.fLog_fExp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:33:32.783994+00:00
-- url     : https://prove2.me/submissions/b27d5aa6-d04f-474e-b1fa-30035e4b4361

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Theorems.Thm_Formalism_L2_Th1_B_log_subst_exp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B
open PowerSeries
variable {K : Type} [Field K] [CharZero K] {ι : Type}
namespace Formalism.L2.Th1.B
theorem _root_.solution {f : MvPowerSeries ι K} (hf : MvPowerSeries.constantCoeff f = 0) :
    fLog (fExp f) = f := by
  have hE : constantCoeff (exp K - 1 : PowerSeries K) = 0 := by simp
  have hf' : HasSubst f := HasSubst.of_constantCoeff_zero hf
  unfold fLog fExp
  have e : (exp K).subst f - 1 = (exp K - 1 : PowerSeries K).subst f := by
    rw [← coe_substAlgHom hf', map_sub, map_one]
  rw [e, ← subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' hE) hf',
    log_subst_exp, subst_X hf']
end Formalism.L2.Th1.B
