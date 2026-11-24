-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.EDec.A_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:11:46.347802+00:00
-- url     : https://prove2.me/submissions/35acf56d-17f6-49e3-9042-6a46f1bc5a22

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TheoremSFromKOneOf
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EDecomp
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_EDec_A_term
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
        ∑ ab : Fin r0 × Fin r1, Ts1 TT ξ p E s ab * Ts2 TT ξ p E s ab =
      ∑ φ : PhiI ν r0 r1 E,
        MvPowerSeries.C (aAof p u TT ξ φ) * topMonoS (Lw := ZV ν r0 r1) (dAof p φ) := by
  symm
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  calc _ = ∑ l : Fin E, ∑ ab : Fin r0 × Fin r1, ∑ l' : Fin E,
        MvPowerSeries.C (aAof p u TT ξ (s, l, l', ab)) *
          topMonoS (Lw := ZV ν r0 r1) (dAof p (s, l, l', ab)) := by
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Fintype.sum_prod_type, Finset.sum_comm]
    _ = _ := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun ab _ => ?_
        rw [Ts1, Ts2, Finset.sum_range, Finset.sum_range, Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun l' _ => (A_term hp u TT ξ s l l' ab).symm
end Formalism.InvariantFactorPaths.G7.EDec
