-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.TwoVariableSwapLemmas.swap_two_frobenius
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:44:58.901567+00:00
-- url     : https://prove2.me/submissions/97393f7d-3837-45f6-b362-54528d18fd38

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_ScalingSwapLemmas
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoVariableSwapLemmas_hasSubst_swap
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_frobVar_eq_expand


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
theorem _root_.solution {p : ℕ} (hp : p ≠ 0) (f : MvPowerSeries (Fin 2) K) :
    swap2 (frobVar p f) = frobVar p (swap2 f) := by
  rw [frobVar_eq_expand hp (swap2 f)]
  unfold swap2 frobVar
  rw [expand_subst p hp hasSubst_swap, subst_comp_subst_apply (HasSubst.X_pow hp) hasSubst_swap]
  congr 1
  funext i
  fin_cases i <;> simp [subst_pow hasSubst_swap, subst_X hasSubst_swap]
end Formalism.InvariantFactorPaths.G7.TwoVariableSwapLemmas
