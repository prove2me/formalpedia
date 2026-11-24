-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.TwoVariableSwapLemmas.partial_coboundary_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:52:32.148841+00:00
-- url     : https://prove2.me/submissions/d1641369-3d0f-49ec-86ee-f1a4aa9faa4e

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_ScalingSwapLemmas
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoVariableSwapLemmas_diffOne_add
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoVariableSwapLemmas_partial_coboundary_C_mul

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
theorem _root_.solution {F : MvPowerSeries (Fin 2) K} (hF : constantCoeff F = 0) (s : Finset ℕ)
    (f : ℕ → MvPowerSeries (Fin 2) K) : d1 F (∑ k ∈ s, f k) = ∑ k ∈ s, d1 F (f k) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h := partial_coboundary_C_mul hF 0 (0 : MvPowerSeries (Fin 2) K)
    simpa using h
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, diffOne_add hF, ih]
end Formalism.InvariantFactorPaths.G7.TwoVariableSwapLemmas
