-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.ThmSCore_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:19:55.370616+00:00
-- url     : https://prove2.me/submissions/55331df4-fff8-4b7c-9d12-5838a7b84a6b

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_CyclicPowerClassOfExpEquiv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Definitions.Def_Lemmata_GeneralBFactRightExtra_Imports
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TheoremSFromKOneOf
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_pinv_le_one
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_integral_neg
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_integral_C
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_integral_X
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_constantCoeff_sSub
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_integral_sSub
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_subst_exp_Gtot
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_low_subst_of_low
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_norm_finsum_le_of
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integralSubstV
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_mul
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_one
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_pow
import Theorems.Thm_Formalism_FG_SolveVAux_low_one_iff
import Theorems.Thm_Formalism_FG_SolveVAux_low_pow
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_constant_coeff_hh_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral mvExp low_subst_of_low norm_finsum_le_of)
open Formalism.FG.SolveVAux (Low low_pow low_one_iff)
open Formalism.FG.IntegralSubstitution (integral_mul integral_pow integral_one integralSubstV)
open TwoS
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution (h1 : RescaleCore) (h2 : ClassSubst) (h3 : ClassChange) (h4 : ClassMul)
    (h5 : TwoSums) (h6 : LogRescale) (h7 : LogRescaleUnique) : ThmSCore := by
  intro K _ _ _ p ν r0 r1 _ om oms c c' ϖ μ U hp hn hϖ hO hc hc' hμ0 hμ hU
  have hpK : (p : K) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  obtain ⟨-, -, μ0, hμ00, -, hμ0s, -, hμa⟩ := h6 K p ϖ hp hn hϖ
  obtain rfl : μ = μ0 := h7 K p ϖ μ μ0 hp.two_le hpK hμ0 hμ00 hμ hμ0s
  have hϖ1 : ‖ϖ‖ ≤ 1 := by
    by_contra hlt
    replace hlt := not_le.1 hlt
    have hN : p ^ 2 - 1 ≠ 0 := by
      have : 4 ≤ p ^ 2 := by nlinarith [hp.two_le]
      omega
    have h := one_lt_pow₀ hlt hN
    rw [← norm_pow, hϖ, hn] at h
    exact absurd h (not_lt.2 (pinv_le_one p))
  have hφ0 := constantCoeff_sSub (r0 := r0) (r1 := r1) om oms hμ0
  have hφI := integral_sSub (r0 := r0) (r1 := r1) hp hn hO hμa
  have hsφ : MvPowerSeries.HasSubst (sSub (r0 := r0) (r1 := r1) om oms μ) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero hφ0
  have hψ0 : ∀ x : Bool × EV ν r0 r1, MvPowerSeries.constantCoeff (MvPowerSeries.C ϖ *
      (MvPowerSeries.X x : MvPowerSeries (Bool × EV ν r0 r1) K)) = 0 := fun x => by simp
  have hψI : ∀ x : Bool × EV ν r0 r1, Integral (MvPowerSeries.C ϖ *
      (MvPowerSeries.X x : MvPowerSeries (Bool × EV ν r0 r1) K)) := fun x =>
    integral_mul (integral_C hϖ1) (integral_X x)
  have hsψ := MvPowerSeries.hasSubst_of_constantCoeff_zero hψ0
  have e0 : (fun x => MvPowerSeries.C ϖ * sSub (r0 := r0) (r1 := r1) om oms μ x) =
      fun x => MvPowerSeries.subst (sSub om oms μ) (MvPowerSeries.C ϖ *
        (MvPowerSeries.X x : MvPowerSeries (Bool × EV ν r0 r1) K)) := by
    funext x
    rw [MvPowerSeries.subst_mul hsφ, MvPowerSeries.subst_C, MvPowerSeries.subst_X hsφ]
  rw [e0, ← MvPowerSeries.subst_comp_subst_apply hsψ hsφ, MvPowerSeries.subst_mul hsψ,
    subst_exp_Gtot hp.ne_zero]
  have hh0 := constant_coeff_hh_zero (E := EV ν r0 r1) hp.ne_zero c c'
  have a1 := h1 K (EV ν r0 r1) p c c' ϖ hp hn hϖ hc hc'
  have a2 := h4 K _ (p : K) _ _ _ hh0 (integralSubstV U _ hU hψ0 hψI) a1
  have a3 := h2 K _ _ (p : K) _ _ _ hh0 hφ0 hφI a2
  obtain ⟨Y, hY, hY0, hYe⟩ := h5 K p ν r0 r1 om oms c c' μ hp hn hO hc hc' hμ0 hμa
  have a4 := h3 K _ (p : K) hpK (by rw [hn]; exact pinv_le_one p) _ (-Y) _
    (MvPowerSeries.constantCoeff_subst_eq_zero hsφ hφ0 hh0) (by rw [map_neg, hY0, neg_zero])
    (integral_neg hY) a3
  have e1 : MvPowerSeries.subst (sSub om oms μ) (hh1 (E := EV ν r0 r1) p c c') +
      MvPowerSeries.C (p : K) * -Y = hhS p (uS c c') := by
    rw [hYe]; ring
  rwa [e1] at a4
end Formalism.InvariantFactorPaths.G7
