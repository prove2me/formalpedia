-- Prove2me | solution 1 for Formalism.L2.Th1.B.pd_fExp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:20:10.828549+00:00
-- url     : https://prove2.me/submissions/f4aa0c30-fbb2-4e72-89ea-908a593d080a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Theorems.Thm_Formalism_G_LogCR_pderiv_psubst

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
private theorem derivative_exp_eq_exp : derivative K (exp K) = exp K := by
  ext n
  rw [PowerSeries.coeff_derivative]
  simp [coeff_exp, Nat.factorial_succ]
  field_simp
private theorem pderiv_exp_subst_eq_mul_pderiv {ι : Type} [Finite ι] (i : ι) {f : MvPowerSeries ι K}
    (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.pderiv K i ((exp K).subst f) = (exp K).subst f * MvPowerSeries.pderiv K i f := by
  rw [Formalism.G.LogCR.pderiv_psubst hf, derivative_exp_eq_exp]
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
theorem _root_.solution [Finite ι] (i : ι) {f : MvPowerSeries ι K}
    (hf : MvPowerSeries.constantCoeff f = 0) : pd i (fExp f) = fExp f * pd i f :=
  pderiv_exp_subst_eq_mul_pderiv i hf
end Formalism.L2.Th1.B
