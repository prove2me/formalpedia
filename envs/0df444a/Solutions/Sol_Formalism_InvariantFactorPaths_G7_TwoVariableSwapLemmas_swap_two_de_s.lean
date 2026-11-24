-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.TwoVariableSwapLemmas.swap_two_de_s
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:45:56.528615+00:00
-- url     : https://prove2.me/submissions/f547a42f-4363-4c67-a904-9c75092b83f7

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_ScalingSwapLemmas
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoVariableSwapLemmas_swap_two_sub
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoVariableSwapLemmas_swap_two_C_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoVariableSwapLemmas_swap_two_map
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoVariableSwapLemmas_swap_two_frobenius

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
theorem _root_.solution {p : ℕ} (hp : p ≠ 0) (σ : K →+* K) (G : MvPowerSeries (Fin 2) K) :
    DeS p σ (swap2 G) = swap2 (DeS p σ G) := by
  unfold DeS
  rw [swap_two_C_mul, swap_two_sub, swap_two_C_mul, swap_two_frobenius hp, swap_two_map]
end Formalism.InvariantFactorPaths.G7.TwoVariableSwapLemmas
