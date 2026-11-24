-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.TwoVariableSwapLemmas.diffOne_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:45:53.525032+00:00
-- url     : https://prove2.me/submissions/220f6cc6-509e-4408-b58e-dd18391df477

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_ScalingSwapLemmas
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoVariableSwapLemmas_has_subst_coboundary_first
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoVariableSwapLemmas_has_subst_last_pair

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
theorem _root_.solution {F : MvPowerSeries (Fin 2) K} (hF : constantCoeff F = 0)
    (H H' : MvPowerSeries (Fin 2) K) : d1 F (H + H') = d1 F H + d1 F H' := by
  unfold d1
  rw [subst_add (has_subst_coboundary_first hF), subst_add (has_subst_last_pair 0), subst_add (has_subst_last_pair 1)]
  ring
end Formalism.InvariantFactorPaths.G7.TwoVariableSwapLemmas
