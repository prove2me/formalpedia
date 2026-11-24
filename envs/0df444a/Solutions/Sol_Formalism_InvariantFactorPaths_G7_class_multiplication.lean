-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.class_multiplication
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:46:38.427552+00:00
-- url     : https://prove2.me/submissions/ac8ae88f-4559-401e-9530-c5228ec339d5

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_OddLogRelation
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_LogarithmWeightComparison
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_IntegralSubstVector
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_inClass_iff
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_dot_const
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_low_subst_of_low
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_substitution_weight_bound
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_mul
import Theorems.Thm_Formalism_FG_SolveVAux_low_add
import Theorems.Thm_Formalism_FG_SolveVAux_low_mono
import Theorems.Thm_Formalism_FG_SolveVAux_low_mul
import Theorems.Thm_Formalism_FG_SolveVAux_low_neg
import Theorems.Thm_Formalism_FG_SolveVAux_low_one_iff
import Theorems.Thm_Formalism_FG_SolveVAux_low_pow
import Theorems.Thm_Formalism_FG_SolveVAux_low_sub
import Theorems.Thm_Formalism_FG_SolveVAux_low_zero


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
open Formalism.DworkPowerSeriesWeights (Integral mvExp low_subst_of_low WtGe MonoWtGe dot dot_const substitution_weight_bound)
open Formalism.FG.SolveVAux (Low low_zero low_mono low_add low_sub low_neg low_mul low_pow low_one_iff)
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution : ClassMul := by
  intro K ι _ _ pp hh F V h0 hV hF
  rw [inClass_iff h0] at hF ⊢
  obtain ⟨U, hU, h⟩ := hF
  refine ⟨fun i => U i * V, fun i => Formalism.FG.IntegralSubstitution.integral_mul (hU i) hV, fun M => ?_⟩
  have e : F * V - clSum pp hh (fun i => U i * V) M = (F - clSum pp hh U M) * V := by
    simp only [clSum, sub_mul, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e]
  simpa using low_mul (h M) (low_zero V)
end Formalism.InvariantFactorPaths.G7
