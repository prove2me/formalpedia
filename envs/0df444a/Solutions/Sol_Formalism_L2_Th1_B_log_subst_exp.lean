-- Prove2me | solution 1 for Formalism.L2.Th1.B.log_subst_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:22:04.892505+00:00
-- url     : https://prove2.me/submissions/1b89c8ac-5fa8-4ab6-88af-26e4719f61cd

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Theorems.Thm_Formalism_L2_Th1_B_one_add_mul_deriv_log_subst
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
private theorem constantCoeff_powerSeries_subst_mv_eq {ι : Type} (φ : PowerSeries K) {f : MvPowerSeries ι K}
    (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (φ.subst f) = constantCoeff φ := by
  rw [PowerSeries.constantCoeff_subst (HasSubst.of_constantCoeff_zero hf), finsum_eq_single _ 0]
  · simp
  · intro d hd
    simp [hf, zero_pow hd]
private theorem constantCoeff_powerSeries_subst_eq (φ : PowerSeries K) {g : PowerSeries K}
    (hg : constantCoeff g = 0) : constantCoeff (φ.subst g) = constantCoeff φ :=
  constantCoeff_powerSeries_subst_mv_eq φ (f := g) hg
private theorem constantCoeff_log_eq_zero' : constantCoeff (log K) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  simp [PowerSeries.log]
private theorem derivative_exp_eq_exp : derivative K (exp K) = exp K := by
  ext n
  rw [PowerSeries.coeff_derivative]
  simp [coeff_exp, Nat.factorial_succ]
  field_simp
private theorem derivative_eq_pderiv_unit (f : PowerSeries K) :
    derivative K f = MvPowerSeries.pderiv K () f := by
  ext n
  rw [PowerSeries.coeff_derivative]
  change _ = MvPowerSeries.coeff (Finsupp.single () n) _
  rw [MvPowerSeries.coeff_pderiv, ← Finsupp.single_add, Finsupp.single_eq_same]
  rfl
private theorem derivative_subst_eq_chain_rule {g : PowerSeries K} (hg : constantCoeff g = 0)
    (φ : PowerSeries K) :
    derivative K (φ.subst g) = (derivative K φ).subst g * derivative K g := by
  have h := Formalism.G.LogCR.pderiv_psubst (R := K) (τ := Unit) (a := g) hg φ ()
  simp only [derivative_eq_pderiv_unit]
  exact h
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
theorem _root_.solution : (log K).subst (exp K - 1) = X := by
  have hc : constantCoeff (exp K - 1 : PowerSeries K) = 0 := by simp
  apply derivative.ext
  · rw [derivative_subst_eq_chain_rule hc, derivative_X, map_sub, derivative_exp_eq_exp, Derivation.map_one_eq_zero,
      sub_zero]
    have h := one_add_mul_deriv_log_subst (HasSubst.of_constantCoeff_zero' hc)
    have e : (1 : PowerSeries K) + (exp K - 1) = exp K := by ring
    rw [e] at h
    rw [mul_comm]
    exact h
  · rw [constantCoeff_powerSeries_subst_eq _ hc, constantCoeff_log_eq_zero']
    simp
end Formalism.L2.Th1.B
