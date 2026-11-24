-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.EDec.cg_first
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:45:09.777671+00:00
-- url     : https://prove2.me/submissions/434d0e6b-9678-4f39-bab0-caa9e05314e6

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TheoremSFromKOneOf
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EDecomp
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_EDec_integral_negOnePow
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_EDec_cg_frob_add_pow
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
variable {K ι : Type} [NormedField K] [IsUltrametricDist K]
namespace Formalism.InvariantFactorPaths.G7.EDec
theorem _root_.solution {p : ℕ} (hp : p.Prime) (h2 : 2 < p) (hn : ‖(p : K)‖ = (p : ℝ)⁻¹) (E : ℕ)
    (z t : ℕ → MvPowerSeries ι K) (hz : ∀ l, Integral (z l)) (ht : ∀ l, Integral (t l)) :
    Cg p ((∑ l ∈ range E, (-1) ^ l * (z l + t l) ^ ((p ^ 2) ^ l)) ^ p)
      (∑ l ∈ range E, (-1) ^ l * z l ^ (p ^ (1 + 2 * l)) +
        ∑ l ∈ range E, (-1) ^ l * t l ^ (p ^ (1 + 2 * l))) := by
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  refine cg_trans (cg_frob_sum hp hn _ _ fun l _ =>
    integral_mul (integral_negOnePow l) (integral_pow (integral_add (hz l) (ht l)) _)) ?_
  rw [← Finset.sum_add_distrib]
  refine cg_sum _ _ _ fun l _ => ?_
  have e1 : ((-1 : MvPowerSeries ι K) ^ l) ^ p = (-1) ^ l := by
    rw [← pow_mul, mul_comm, pow_mul, hodd.neg_one_pow]
  have e2 : ((z l + t l) ^ ((p ^ 2) ^ l)) ^ p = (z l + t l) ^ (p ^ (1 + 2 * l)) := by
    rw [← pow_mul, ← pow_mul, ← pow_succ, add_comm 1 (2 * l)]
  rw [mul_pow, e1, e2, ← mul_add]
  exact cg_mul (integral_negOnePow l) (integral_add (integral_pow (hz l) _) (integral_pow (ht l) _))
    (cg_refl p _) (cg_frob_add_pow hp hn (hz l) (ht l) _)
end Formalism.InvariantFactorPaths.G7.EDec
