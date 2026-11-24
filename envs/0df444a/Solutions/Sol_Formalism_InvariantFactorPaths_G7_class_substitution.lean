-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.class_substitution
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:46:39.781803+00:00
-- url     : https://prove2.me/submissions/1739e606-d36c-47c5-b568-ec4a756b0e77

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
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integralSubstV
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
theorem _root_.solution : ClassSubst := by
  intro K ι κ _ _ _ pp hh F φ h0 hφ0 hφ hF
  have hs : MvPowerSeries.HasSubst φ := MvPowerSeries.hasSubst_of_constantCoeff_zero hφ0
  have h0' : MvPowerSeries.constantCoeff (MvPowerSeries.subst φ hh) = 0 :=
    (low_one_iff _).1 (low_subst_of_low hφ0 ((low_one_iff _).2 h0))
  rw [inClass_iff h0] at hF
  rw [inClass_iff h0']
  obtain ⟨U, hU, h⟩ := hF
  refine ⟨fun i => MvPowerSeries.subst φ (U i),
    fun i => Formalism.FG.IntegralSubstitution.integralSubstV _ _ (hU i) hφ0 hφ, fun M => ?_⟩
  have e : MvPowerSeries.subst φ F -
      clSum pp (MvPowerSeries.subst φ hh) (fun i => MvPowerSeries.subst φ (U i)) M =
      MvPowerSeries.subst φ (F - clSum pp hh U M) := by
    simp only [clSum, ← MvPowerSeries.coe_substAlgHom hs, map_sub, map_sum, map_mul, map_pow]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    exact ((MvPowerSeries.substAlgHom hs).commutes ((pp ^ i)⁻¹)).symm
  rw [e]
  exact low_subst_of_low hφ0 (h M)
end Formalism.InvariantFactorPaths.G7
