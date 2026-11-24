-- Prove2me | solution 1 for Formalism.L2.Th1.B.exp_subst_log
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:21:21.372438+00:00
-- url     : https://prove2.me/submissions/acb748a0-657d-4f1a-989c-527dd968d6b3

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Theorems.Thm_Formalism_L2_Th1_B_one_add_X_mul_deriv_log
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
private theorem eq_zero_of_one_add_X_mul_derivative_eq_self {F : PowerSeries K}
    (h : (1 + X) * derivative K F = F) (h0 : constantCoeff F = 0) : F = 0 := by
  ext n
  rw [map_zero]
  induction n with
  | zero => simpa using h0
  | succ n ih =>
    have hn := congrArg (coeff n) h
    rw [add_mul, one_mul, map_add, PowerSeries.coeff_derivative] at hn
    rcases n with _ | m
    · rw [coeff_zero_X_mul] at hn
      simpa [ih] using hn
    · rw [coeff_succ_X_mul, PowerSeries.coeff_derivative, ih] at hn
      have hne : ((m : K) + 1 + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (m + 1)
      simpa [hne] using hn
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
theorem _root_.solution : (exp K).subst (log K) = 1 + X := by
  have hl : constantCoeff (log K) = 0 := constantCoeff_log_eq_zero'
  have hE : derivative K ((exp K).subst (log K)) =
      (exp K).subst (log K) * derivative K (log K) := by
    rw [derivative_subst_eq_chain_rule hl, derivative_exp_eq_exp]
  rw [← sub_eq_zero]
  apply eq_zero_of_one_add_X_mul_derivative_eq_self
  · rw [map_sub, hE, map_add, Derivation.map_one_eq_zero, derivative_X, zero_add, mul_sub, mul_one,
      mul_left_comm, one_add_X_mul_deriv_log, mul_one]
  · rw [map_sub, constantCoeff_powerSeries_subst_eq _ hl]
    simp
end Formalism.L2.Th1.B
