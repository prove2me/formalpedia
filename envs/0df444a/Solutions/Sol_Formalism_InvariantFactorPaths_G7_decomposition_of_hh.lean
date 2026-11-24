-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.decomposition_of_hh
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:17:45.457419+00:00
-- url     : https://prove2.me/submissions/e2743e3c-7f98-401e-a5cf-6bd8bf9f88c7

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TheoremSFromKOneOf
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EDecomp
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_EDec_lowGe_add
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_EDec_lowGe_sum
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_EDec_lowGe_mul_right
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_EDec_lowGe_mul_left
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_EDec_cg_second
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_EDec_cg_first
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_EDec_exists_of_cg
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_EDec_low_hh_sub
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_EDec_constantCoeff_zSub
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_EDec_subst_sT
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_EDec_subst_hhT
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_EDec_sort_prod
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_EDec_A_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_EDec_B_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_EDec_integral_zlS
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_EDec_integral_tpS
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_EDec_integral_altSum
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_EDec_integral_second_sum_variant
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_EDec_low_order_first_sum
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_EDec_low_order_second_sum_variant
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_low_subst_of_low
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_mul
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_one
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_pow
import Theorems.Thm_Formalism_FG_SolveVAux_low_add
import Theorems.Thm_Formalism_FG_SolveVAux_low_mono
import Theorems.Thm_Formalism_FG_SolveVAux_low_mul
import Theorems.Thm_Formalism_FG_SolveVAux_low_mul_sub
import Theorems.Thm_Formalism_FG_SolveVAux_low_of_zero
import Theorems.Thm_Formalism_FG_SolveVAux_low_one_iff
import Theorems.Thm_Formalism_FG_SolveVAux_low_pow
import Theorems.Thm_Formalism_FG_SolveVAux_low_sub
import Theorems.Thm_Formalism_FG_SolveVAux_low_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_add
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_frob_add
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_frob_sum
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_of_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_pow
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_refl
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_sum
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_symm
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_trans
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_coeff_sPos
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_integral_C
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_integral_X
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_integral_add
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_integral_neg
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_integral_sum
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_integral_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_pinv_nonneg


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
open Formalism.DworkPowerSeriesWeights (Integral low_subst_of_low)
open Formalism.FG.SolveVAux (Low low_zero low_mono low_add low_sub low_mul low_pow low_one_iff low_mul_sub
  low_of_zero)
open Formalism.FG.IntegralSubstitution (integral_mul integral_pow integral_one)
open TwoS (Cg cg_refl cg_of_eq cg_symm cg_trans cg_add cg_sum cg_mul cg_pow cg_frob_add cg_frob_sum
  integral_add integral_neg integral_sum integral_C integral_X integral_zero coeff_sPos pinv_nonneg)
open EDec
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution : HhDecomp := by
  intro K _ _ p ν r0 r1 E D _ u TT ξ hp h2 hn hu hξ hD
  have hp0 : p ≠ 0 := hp.ne_zero
  have hs : MvPowerSeries.HasSubst (zSub (r1 := r1) TT ξ) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (constantCoeff_zSub TT ξ)

  have hcg : Cg p (MvPowerSeries.subst (zSub TT ξ) (hhT (r0 := r0) (r1 := r1) p E u))
      (∑ s : ZMod (2 * ν), MvPowerSeries.C (u s) * ∑ ab : Fin r0 × Fin r1,
        (Zs1 p E s ab + Ts1 TT ξ p E s ab) * (Zs2 p E s ab + Ts2 TT ξ p E s ab)) := by
    rw [subst_hhT]
    refine cg_sum _ _ _ fun s _ => ?_
    have hI2 : ∀ ab : Fin r0 × Fin r1, Integral (Zs2 (K := K) p E s ab + Ts2 TT ξ p E s ab) :=
      fun ab => integral_add (integral_altSum E _ _ fun l => integral_zlS _)
        (integral_altSum E _ _ fun l => integral_tpS TT hξ _)
    refine cg_mul (integral_C (hu s)) (integral_sum _ _ fun ab _ => integral_mul
      (integral_add (integral_altSum E _ _ fun l => integral_zlS _)
        (integral_altSum E _ _ fun l => integral_tpS TT hξ _)) (hI2 ab)) (cg_refl p _) ?_
    refine cg_sum _ _ _ fun ab _ => ?_
    rw [subst_sT, subst_sT]
    refine cg_mul (integral_pow (integral_altSum E _ _ fun l =>
      integral_add (integral_zlS _) (integral_tpS TT hξ _)) p) (hI2 ab) ?_ ?_
    · exact cg_first hp h2 hn E _ _ (fun l => integral_zlS _) (fun l => integral_tpS TT hξ _)
    · exact cg_second hp hn E _ _ (fun l => integral_zlS _) (fun l => integral_tpS TT hξ _)
  obtain ⟨Y, hY, hYe⟩ := exists_of_cg hp hn hcg
  refine ⟨∑ s : ZMod (2 * ν), MvPowerSeries.C (u s) * ∑ ab : Fin r0 × Fin r1,
      (Zs1 p E s ab * (Zs2 p E s ab + Ts2 TT ξ p E s ab) + Ts1 TT ξ p E s ab * Zs2' p E s ab),
    Y, ?_, hY, ?_, ?_⟩
  · refine integral_sum _ _ fun s _ => integral_mul (integral_C (hu s))
      (integral_sum _ _ fun ab _ => integral_add (integral_mul ?_ (integral_add ?_ ?_))
        (integral_mul ?_ (integral_second_sum_variant p E s ab)))
    · exact integral_altSum E _ _ fun l => integral_zlS _
    · exact integral_altSum E _ _ fun l => integral_zlS _
    · exact integral_altSum E _ _ fun l => integral_tpS TT hξ _
    · exact integral_altSum E _ _ fun l => integral_tpS TT hξ _
  · exact lowGe_sum _ _ fun s _ => lowGe_mul_left (lowGe_sum _ _ fun ab _ =>
      lowGe_add (lowGe_mul_right (low_order_first_sum p E s ab) _) (lowGe_mul_left (low_order_second_sum_variant p E s ab) _)) _
  · intro n hnD
    have hlow : Low ((p ^ 2) ^ E) (MvPowerSeries.subst (zSub TT ξ)
        (hhS (r0 := r0) (r1 := r1) p u - hhT p E u)) :=
      low_subst_of_low (constantCoeff_zSub TT ξ) (low_hh_sub hp.two_le E u)
    have h0 := hlow n (by rw [← pow_mul]; omega)
    rw [MvPowerSeries.subst_sub hs, map_sub, sub_eq_zero] at h0
    rw [h0, hYe, ← A_eq hp0 E u TT ξ, ← B_eq hp0 E u TT ξ]
    congr 2
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← mul_add, ← mul_add, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl fun ab _ => sort_prod TT ξ p E s ab
end Formalism.InvariantFactorPaths.G7
