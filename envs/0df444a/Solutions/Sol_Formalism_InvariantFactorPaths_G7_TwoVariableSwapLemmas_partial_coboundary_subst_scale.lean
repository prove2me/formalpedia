-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.TwoVariableSwapLemmas.partial_coboundary_subst_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:45:54.915886+00:00
-- url     : https://prove2.me/submissions/af58655f-49ab-4a31-8f76-b98a7c4c4127

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_ScalingSwapLemmas
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoVariableSwapLemmas_has_subst_scale_two
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoVariableSwapLemmas_has_subst_scale_three
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoVariableSwapLemmas_subst_scale_three_X_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoVariableSwapLemmas_subst_scale_three_X_one
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoVariableSwapLemmas_subst_scale_three_X_two
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoVariableSwapLemmas_has_subst_coboundary_first
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoVariableSwapLemmas_has_subst_last_pair
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoVariableSwapLemmas_subst_scale_three_include

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
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7.TwoVariableSwapLemmas
open MvPowerSeries
variable {K : Type} [Field K]
namespace Formalism.InvariantFactorPaths.G7.TwoVariableSwapLemmas
theorem _root_.solution {F : MvPowerSeries (Fin 2) K} (hF : constantCoeff F = 0) {u : K} (v : K)
    (hu : subst (fun a : Fin 2 => C u * (X a : MvPowerSeries (Fin 2) K)) F = C u * F)
    (H : MvPowerSeries (Fin 2) K) :
    d1 F (subst (sc2 u v) H) = subst (sc3 u v) (d1 F H) := by
  unfold d1
  rw [subst_sub (has_subst_scale_three u v), subst_sub (has_subst_scale_three u v),
    subst_comp_subst_apply (has_subst_scale_two u v) (has_subst_coboundary_first hF), subst_comp_subst_apply (has_subst_scale_two u v) (has_subst_last_pair 0),
    subst_comp_subst_apply (has_subst_scale_two u v) (has_subst_last_pair 1),
    subst_comp_subst_apply (has_subst_coboundary_first hF) (has_subst_scale_three u v), subst_comp_subst_apply (has_subst_last_pair 0) (has_subst_scale_three u v),
    subst_comp_subst_apply (has_subst_last_pair 1) (has_subst_scale_three u v)]
  congr 1
  · congr 1
    · congr 1
      funext i
      fin_cases i <;>
        simp [subst_mul (has_subst_coboundary_first hF), subst_X (has_subst_coboundary_first hF), subst_scale_three_X_two, sc2, subst_scale_three_include v hu]
    · congr 1
      funext i
      fin_cases i <;>
        simp [subst_mul (has_subst_last_pair 0), subst_X (has_subst_last_pair 0), subst_scale_three_X_zero, subst_scale_three_X_two, sc2]
  · congr 1
    funext i
    fin_cases i <;>
      simp [subst_mul (has_subst_last_pair 1), subst_X (has_subst_last_pair 1), subst_scale_three_X_one, subst_scale_three_X_two, sc2]
end Formalism.InvariantFactorPaths.G7.TwoVariableSwapLemmas
