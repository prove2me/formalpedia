-- Prove2me | solution 1 for Formalism.L2.Th1.B.exp_biv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:21:20.042777+00:00
-- url     : https://prove2.me/submissions/97f7b974-2865-4cac-b6c2-3e109b2ea2fa

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
private theorem constantCoeff_powerSeries_subst_mv_eq {ι : Type} (φ : PowerSeries K) {f : MvPowerSeries ι K}
    (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (φ.subst f) = constantCoeff φ := by
  rw [PowerSeries.constantCoeff_subst (HasSubst.of_constantCoeff_zero hf), finsum_eq_single _ 0]
  · simp
  · intro d hd
    simp [hf, zero_pow hd]
private theorem derivative_exp_eq_exp : derivative K (exp K) = exp K := by
  ext n
  rw [PowerSeries.coeff_derivative]
  simp [coeff_exp, Nat.factorial_succ]
  field_simp
private theorem eq_zero_of_forall_pderiv_eq_self {σ : Type} {u : MvPowerSeries σ K}
    (hu : ∀ i, MvPowerSeries.pderiv K i u = u) (h0 : MvPowerSeries.constantCoeff u = 0) :
    u = 0 := by
  classical
  suffices H : ∀ N : ℕ, ∀ n : σ →₀ ℕ, n.degree = N → MvPowerSeries.coeff n u = 0 by
    ext n
    simpa using H _ n rfl
  intro N
  induction N with
  | zero =>
    intro n hn
    rw [Finsupp.degree_eq_zero_iff] at hn
    subst hn
    simpa using h0
  | succ N ih =>
    intro n hn
    obtain ⟨i, hi⟩ : ∃ i, n i ≠ 0 := by
      by_contra hc
      push_neg at hc
      have : n = 0 := by
        ext j
        exact hc j
      subst this
      simp at hn
    set m := n - Finsupp.single i 1 with hm
    have hnm : n = m + Finsupp.single i 1 := by
      ext j
      simp only [hm, Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
        Finsupp.single_apply]
      split_ifs with hij
      · subst hij
        omega
      · omega
    have hadd : (m + Finsupp.single i 1).degree = m.degree + 1 := by
      rw [map_add, Finsupp.degree_single]
    have hdeg : m.degree = N := by
      rw [← hnm] at hadd
      omega
    have key := congrArg (MvPowerSeries.coeff m) (hu i)
    rw [MvPowerSeries.coeff_pderiv, ih m hdeg, ← hnm] at key
    have hne : ((m i : K) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (m i)
    simpa [hne] using key
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
variable {K : Type} [Field K] [CharZero K]
namespace Formalism.L2.Th1.B
theorem _root_.solution :
    (exp K).subst (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) =
      (exp K).subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) *
        (exp K).subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) := by
  have h0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have h1 : MvPowerSeries.constantCoeff (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have h01 : MvPowerSeries.constantCoeff
      (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 := by simp
  rw [← sub_eq_zero]
  apply eq_zero_of_forall_pderiv_eq_self
  · intro i
    rw [map_sub, Derivation.leibniz, pderiv_exp_subst_eq_mul_pderiv i h01, pderiv_exp_subst_eq_mul_pderiv i h0,
      pderiv_exp_subst_eq_mul_pderiv i h1, map_add, smul_eq_mul, smul_eq_mul]
    fin_cases i <;> simp <;> ring
  · rw [map_sub, map_mul, constantCoeff_powerSeries_subst_mv_eq _ h01, constantCoeff_powerSeries_subst_mv_eq _ h0,
      constantCoeff_powerSeries_subst_mv_eq _ h1]
    simp
end Formalism.L2.Th1.B
