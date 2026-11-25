-- Prove2me | solution 1 for Formalism.LT.CongrP.bwd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:00:55.169873+00:00
-- url     : https://prove2.me/submissions/df2cc4cb-cda3-4cba-b7ce-162596688a54

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_SigmaNormLeOne
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_CoeffSubstAddCMulXPow
import Theorems.Thm_Formalism_LT_CongrP_constantCoeff_trunc_succ
import Theorems.Thm_Formalism_LT_CongrP_coeff_subst_trunc
import Theorems.Thm_Formalism_LT_CongrP_coeff_subst_add_C_mul_X_pow
import Theorems.Thm_P2M_Formalism_LT_CongrP_norm_sub_le_max__70c360a457a8
import Theorems.Thm_Formalism_LT_CongrP_fwd
import Theorems.Thm_Formalism_LT_CongrP_integralPS_trunc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
universe u
open Formalism Formalism.LT Formalism.LT.CongrP
open Formalism.G
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
namespace Formalism.LT.CongrP
theorem _root_.solution (h5 : Formalism.LT.CoeffBound.{u}) (h6 : Formalism.LT.PowCongr.{u, 0}) [CharZero K]
    {p q : ℕ} {σ : K →+* K} (hS : FunctionalEquationSetting K p q σ) {f : PowerSeries K}
    (hf0 : constantCoeff f = 0) (hf1 : coeff 1 f = 1) (hfe : IsFunEqType p q σ f)
    {α β : PowerSeries K}
    (hα0 : constantCoeff α = 0) (hβ0 : constantCoeff β = 0) (hα : IntegralPS α)
    (hβ : IntegralPS β) {r : ℕ} (hr : 1 ≤ r)
    (hd : DivBy ((p : K) ^ r) (f.subst α - f.subst β)) :
    DivBy ((p : K) ^ r) (α - β) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rw [coeff_zero_eq_constantCoeff_apply, map_sub, hα0, hβ0, sub_zero, norm_zero]
    exact norm_nonneg _
  set c := coeff N (α - β) with hc
  have hc1 : ‖c‖ ≤ 1 := by
    rw [hc, map_sub]; exact (norm_sub_le_max' _ _).trans (max_le (hα N) (hβ N))
  set β₁ : PowerSeries K := β + C c * X ^ N with hβ₁
  have hcoeffβ₁ : ∀ n, coeff n β₁ = coeff n β + if n = N then c else 0 := by
    intro n
    rw [hβ₁, map_add, coeff_C_mul, coeff_X_pow]
    split_ifs <;> simp
  have hβ₁0 : constantCoeff β₁ = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, hcoeffβ₁, if_neg (by omega), add_zero,
      coeff_zero_eq_constantCoeff_apply, hβ0]
  have hβ₁i : IntegralPS β₁ := fun n => by
    rw [hcoeffβ₁]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hβ n) ?_)
    split_ifs
    · exact hc1
    · simp
  have hdt : DivBy ((p : K) ^ r)
      ((trunc (N + 1) α : PowerSeries K) - (trunc (N + 1) β₁ : PowerSeries K)) := by
    intro n
    rw [map_sub, Polynomial.coeff_coe, Polynomial.coeff_coe, coeff_trunc, coeff_trunc]
    by_cases hn : n < N + 1
    · rw [if_pos hn, if_pos hn, hcoeffβ₁]
      by_cases hnN : n = N
      · subst hnN
        rw [if_pos rfl, hc, map_sub]
        simp
      · rw [if_neg hnN, add_zero, ← map_sub]
        exact ih n (by omega)
    · rw [if_neg hn, if_neg hn, sub_zero, norm_zero]; exact norm_nonneg _
  have hf := fwd h5 h6 hS hf0 hfe (constantCoeff_trunc_succ α hα0 N)
    (constantCoeff_trunc_succ β₁ hβ₁0 N) (integralPS_trunc hα _) (integralPS_trunc hβ₁i _) hr
    hdt N
  rw [map_sub, coeff_subst_trunc f α hα0, coeff_subst_trunc f β₁ hβ₁0] at hf
  have hkey := coeff_subst_add_C_mul_X_pow f β hβ0 c (N := N) hN
  rw [← hβ₁, hf1, one_mul] at hkey
  have hA := hd N
  rw [map_sub] at hA
  have : c = (coeff N (f.subst α) - coeff N (f.subst β)) -
      (coeff N (f.subst α) - coeff N (f.subst β₁)) := by rw [hkey]; ring
  rw [this]
  exact (norm_sub_le_max' _ _).trans (max_le hA hf)
end Formalism.LT.CongrP
