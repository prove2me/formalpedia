-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.two_sums
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:37:56.175448+00:00
-- url     : https://prove2.me/submissions/2e89cd1d-3fc9-405e-b5ca-cf906afbacb5

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_CyclicPowerClassOfExpEquiv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Definitions.Def_Lemmata_GeneralBFactRightExtra_Imports
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TheoremSFromKOneOf
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_constantCoeff_sSub
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_constantCoeff_hhS
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_two_sums
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
theorem _root_.solution : TwoSums := by
  intro K _ _ p ν r0 r1 _ om oms c c' μ hp hn hO hc hc' hμ0 hμ
  have hs : MvPowerSeries.HasSubst (sSub (r0 := r0) (r1 := r1) om oms μ) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (constantCoeff_sSub om oms hμ0)
  have hcg := cg_two_sums (r0 := r0) (r1 := r1) hp hn hO hc hc' hμ0 hμ
  have hpR : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hpK : (p : K) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hn
    exact inv_ne_zero hpR hn.symm
  refine ⟨MvPowerSeries.C ((p : K)⁻¹) *
    (MvPowerSeries.subst (sSub om oms μ) (hh1 (E := EV ν r0 r1) p c c') - hhS p (uS c c')),
    fun n => ?_, ?_, ?_⟩
  · rw [MvPowerSeries.coeff_C_mul, norm_mul, norm_inv, hn, inv_inv]
    calc (p : ℝ) * _ ≤ (p : ℝ) * (p : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_left (hcg n) (Nat.cast_nonneg p)
      _ = 1 := mul_inv_cancel₀ hpR
  · rw [map_mul, map_sub, constantCoeff_hhS hp.ne_zero,
      MvPowerSeries.constantCoeff_subst_eq_zero hs (constantCoeff_sSub om oms hμ0)
        (constant_coeff_hh_zero hp.ne_zero c c'), sub_zero, mul_zero]
  · rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hpK, map_one, one_mul, add_sub_cancel]
end Formalism.InvariantFactorPaths.G7
