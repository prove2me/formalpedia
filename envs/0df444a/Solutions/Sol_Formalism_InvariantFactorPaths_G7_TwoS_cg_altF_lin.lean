-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.TwoS.cg_altF_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:02:21.627836+00:00
-- url     : https://prove2.me/submissions/49519e74-0176-483f-bf23-b6d9d0c33878

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_CyclicPowerClassOfExpEquiv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Definitions.Def_Lemmata_GeneralBFactRightExtra_Imports
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TheoremSFromKOneOf
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_pinv_nonneg
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_coeff_subst_altF
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_constantCoeff_linW
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_coeff_posW
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_lin_pow
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_low_subst_of_low
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_norm_finsum_le_of
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integralSubstV
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_mul
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_one
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_pow
import Theorems.Thm_Formalism_FG_SolveVAux_low_one_iff
import Theorems.Thm_Formalism_FG_SolveVAux_low_pow


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
open Formalism.InvariantFactorPaths.G7.TwoS
variable {K : Type} [NormedField K] [IsUltrametricDist K] {ν r0 r1 : ℕ}
namespace Formalism.InvariantFactorPaths.G7.TwoS
theorem _root_.solution [NeZero ν] {p : ℕ} (hp : p.Prime) (hn : ‖(p : K)‖ = (p : ℝ)⁻¹)
    {w : ZMod (2 * ν) → K} (hw1 : ∀ s, ‖w s‖ ≤ 1)
    (hw2 : ∀ s, ‖w (s + 2) - w s ^ (p ^ 2)‖ ≤ (p : ℝ)⁻¹) (ab : Fin r0 × Fin r1) :
    Cg p (PowerSeries.subst (linW w ab) (altF K p)) (posW p w ab) := by
  intro n
  rw [map_sub, coeff_subst_altF hp.two_le (constantCoeff_linW w ab), coeff_posW,
    ← Finset.sum_sub_distrib]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pinv_nonneg p) fun l _ => ?_
  rw [← mul_sub, ← map_sub, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  exact cg_lin_pow hp hn hw1 hw2 ab l n
end Formalism.InvariantFactorPaths.G7.TwoS
