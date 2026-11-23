-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.GramFrameCompositionLinFacts.subst_swap2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:32:15.740204+00:00
-- url     : https://prove2.me/submissions/a9056cd0-1b34-4741-9a33-0209267c47e0

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_ConstantCoeffLawFirstTwoOfThree
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_GramFrameCompositionLinFacts_subst_subst2

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
open Formalism.InvariantFactorPaths.G7.GramFrameCompositionLinFacts
open MvPowerSeries
variable {K : Type} [Field K]
namespace Formalism.InvariantFactorPaths.G7.GramFrameCompositionLinFacts
theorem _root_.solution {τ : Type} {u v : MvPowerSeries τ K} (h : HasSubst ![u, v])
    (H : MvPowerSeries (Fin 2) K) : subst ![u, v] (swap2 H) = subst ![v, u] H := by
  unfold swap2
  rw [subst_subst2 h HasSubst.X_X, subst_X h, subst_X h]
  rfl
end Formalism.InvariantFactorPaths.G7.GramFrameCompositionLinFacts
