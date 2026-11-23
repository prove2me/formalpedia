-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.norm_unif
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:22:47.953696+00:00
-- url     : https://prove2.me/submissions/d0d7c4ce-00a0-487c-93e1-23c6d511b980

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_OddLogRelation
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_LogarithmWeightComparison
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_IntegralSubstVector
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_dot_const
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_low_subst_of_low
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_substitution_weight_bound
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
theorem _root_.solution {K : Type} [NormedField K] {p : ℕ} (hp : p.Prime) (hn : ‖(p : K)‖ = (p : ℝ)⁻¹)
    {ϖ : K} (hϖ : ϖ ^ (p ^ 2 - 1) = (p : K)) :
    ‖ϖ‖ = ((p : ℝ)⁻¹) ^ (1 / ((p : ℝ) ^ 2 - 1)) := by
  have hp2 := hp.two_le
  have h1 : ‖ϖ‖ ^ (p ^ 2 - 1) = (p : ℝ)⁻¹ := by rw [← norm_pow, hϖ, hn]
  have hsq : 4 ≤ p ^ 2 := by nlinarith
  have hN : p ^ 2 - 1 ≠ 0 := by omega
  have h2 := Real.pow_rpow_inv_natCast (norm_nonneg ϖ) hN
  have hcast : ((p ^ 2 - 1 : ℕ) : ℝ) = (p : ℝ) ^ 2 - 1 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [h1, hcast] at h2
  rw [one_div, h2]
end Formalism.InvariantFactorPaths.G7
