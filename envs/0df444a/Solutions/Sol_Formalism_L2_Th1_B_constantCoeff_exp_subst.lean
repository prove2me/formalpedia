-- Prove2me | solution 1 for Formalism.L2.Th1.B.constantCoeff_exp_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:21:24.206745+00:00
-- url     : https://prove2.me/submissions/da0b4b82-469a-4116-aaf3-02f2482e9be8

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
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
private theorem constantCoeff_powerSeries_subst_mv_eq {ι : Type} (φ : PowerSeries K) {f : MvPowerSeries ι K}
    (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (φ.subst f) = constantCoeff φ := by
  rw [PowerSeries.constantCoeff_subst (HasSubst.of_constantCoeff_zero hf), finsum_eq_single _ 0]
  · simp
  · intro d hd
    simp [hf, zero_pow hd]
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
variable {K : Type} [Field K] [CharZero K]
namespace Formalism.L2.Th1.B
theorem _root_.solution {ι : Type} {f : MvPowerSeries ι K}
    (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff ((exp K).subst f) = 1 := by
  rw [constantCoeff_powerSeries_subst_mv_eq _ hf]
  simp
end Formalism.L2.Th1.B
