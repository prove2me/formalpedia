-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.EDec.B_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:53:25.627804+00:00
-- url     : https://prove2.me/submissions/6667267c-9bd9-4e81-8f6a-f290ff243c35

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TheoremSFromKOneOf
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EDecomp
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_EDec_lowLin_bBof
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_EDec_B_term
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
open Formalism.InvariantFactorPaths.G7.EDec
variable {K : Type} [Field K] {ν r0 r1 : ℕ}
namespace Formalism.InvariantFactorPaths.G7.EDec
theorem _root_.solution [NeZero ν] {p : ℕ} (hp : p ≠ 0) (E : ℕ) (u : ZMod (2 * ν) → K)
    (TT : Finset (ZMod (2 * ν))) (ξ : ZMod (2 * ν) → Fin r0 → K) :
    ∑ s : ZMod (2 * ν), MvPowerSeries.C (u s) *
        ∑ ab : Fin r0 × Fin r1, Ts1 TT ξ p E s ab * zlS (s + 1, ab) =
      ∑ k : KapI ν r1 E,
        MvPowerSeries.C (aBof u TT k) * topMonoS (dBof p k) * lowLin (bBof p ξ k) := by
  symm
  calc _ = ∑ s : ZMod (2 * ν), ∑ l : Fin E, ∑ b : Fin r1, ∑ a : Fin r0,
        MvPowerSeries.C (u (s + 2 * (l.val : ZMod (2 * ν)))) *
          (((-1) ^ l.val * tpS TT ξ (s, (a, b)) ^ (p ^ (1 + 2 * l.val))) *
            zlS (s + 2 * (l.val : ZMod (2 * ν)) + 1, (a, b))) := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun l _ => ?_
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [lowLin_bBof, Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => (B_term hp u TT ξ s l a b).symm
    _ = ∑ l : Fin E, ∑ s : ZMod (2 * ν), ∑ ab : Fin r0 × Fin r1,
        MvPowerSeries.C (u (s + 2 * (l.val : ZMod (2 * ν)))) *
          (((-1) ^ l.val * tpS TT ξ (s, ab) ^ (p ^ (1 + 2 * l.val))) *
            zlS (s + 2 * (l.val : ZMod (2 * ν)) + 1, ab)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ => ?_
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Fintype.sum_prod_type, Finset.sum_comm]
    _ = ∑ l : Fin E, ∑ s : ZMod (2 * ν), ∑ ab : Fin r0 × Fin r1,
        MvPowerSeries.C (u s) *
          (((-1) ^ l.val * tpS TT ξ (s - 2 * (l.val : ZMod (2 * ν)), ab) ^ (p ^ (1 + 2 * l.val))) *
            zlS (s + 1, ab)) := by
        refine Finset.sum_congr rfl fun l _ => ?_
        refine Eq.trans ?_ (Equiv.sum_comp (Equiv.addRight (2 * (l.val : ZMod (2 * ν)))) _)
        simp only [Equiv.coe_addRight, add_sub_cancel_right]
    _ = _ := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Finset.mul_sum, Finset.sum_comm]
        refine Finset.sum_congr rfl fun ab _ => ?_
        rw [Ts1, Finset.sum_range, Finset.sum_mul, Finset.mul_sum]
end Formalism.InvariantFactorPaths.G7.EDec
