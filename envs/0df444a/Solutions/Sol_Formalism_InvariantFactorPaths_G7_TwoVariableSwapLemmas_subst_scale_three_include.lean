-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.TwoVariableSwapLemmas.subst_scale_three_include
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:42:26.845932+00:00
-- url     : https://prove2.me/submissions/a7fe0bd7-32a8-4a09-a267-ec0d4a4e2dd1

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_ScalingSwapLemmas
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoVariableSwapLemmas_has_subst_scale_three
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoVariableSwapLemmas_subst_scale_three_X_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoVariableSwapLemmas_subst_scale_three_X_one
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoVariableSwapLemmas_has_subst_first_pair

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
theorem _root_.solution {F : MvPowerSeries (Fin 2) K} {u : K} (v : K)
    (hu : subst (fun a : Fin 2 => C u * (X a : MvPowerSeries (Fin 2) K)) F = C u * F) :
    subst (sc3 u v) (in3 F) = C u * in3 F := by
  have hs : HasSubst (fun a : Fin 2 => C u * (X a : MvPowerSeries (Fin 2) K)) :=
    hasSubst_of_constantCoeff_zero (by intro i; simp)
  have h1 : C u * in3 F = in3 (C u * F) := by
    unfold in3
    rw [subst_mul has_subst_first_pair, subst_C]
  rw [h1, ← hu]
  unfold in3
  rw [subst_comp_subst_apply has_subst_first_pair (has_subst_scale_three u v), subst_comp_subst_apply hs has_subst_first_pair]
  congr 1
  funext i
  fin_cases i <;> simp [subst_mul has_subst_first_pair, subst_X has_subst_first_pair, subst_scale_three_X_zero, subst_scale_three_X_one]
end Formalism.InvariantFactorPaths.G7.TwoVariableSwapLemmas
