-- Prove2me | solution 1 for Formalism.L2.Th1.B.fExp_fLog
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:31:47.392679+00:00
-- url     : https://prove2.me/submissions/30ebc77a-08d9-4f67-97ef-bdbee80e26a8

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Theorems.Thm_Formalism_L2_Th1_B_one_add_X_subst
import Theorems.Thm_Formalism_L2_Th1_B_exp_subst_log
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace Formalism.L2.Th1.B
open PowerSeries
section One
variable {K : Type} [Field K] [CharZero K]
private theorem constantCoeff_log_eq_zero' : constantCoeff (log K) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  simp [PowerSeries.log]
end One
section Rules
variable {K : Type} [Field K] [CharZero K] {ι : Type}
end Rules
end Formalism.L2.Th1.B
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B
open PowerSeries
variable {K : Type} [Field K] [CharZero K] {ι : Type}
namespace Formalism.L2.Th1.B
theorem _root_.solution {g : MvPowerSeries ι K} (hg : MvPowerSeries.constantCoeff g = 1) :
    fExp (fLog g) = g := by
  have hg1 : MvPowerSeries.constantCoeff (g - 1) = 0 := by simp [hg]
  have hl : constantCoeff (log K) = 0 := constantCoeff_log_eq_zero'
  unfold fExp fLog
  rw [← subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' hl)
    (HasSubst.of_constantCoeff_zero hg1), exp_subst_log,
    one_add_X_subst (HasSubst.of_constantCoeff_zero hg1)]
  ring
end Formalism.L2.Th1.B
