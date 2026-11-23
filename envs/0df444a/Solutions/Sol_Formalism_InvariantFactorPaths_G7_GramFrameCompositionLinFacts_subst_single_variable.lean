-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.GramFrameCompositionLinFacts.subst_single_variable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:32:29.941696+00:00
-- url     : https://prove2.me/submissions/ed88dc2b-c2e9-4327-9496-36d816e19c5f

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_ConstantCoeffLawFirstTwoOfThree
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_GramFrameCompositionLinFacts_subst_psubst

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
theorem _root_.solution {τ κ : Type} {b : τ → MvPowerSeries κ K} (hb : HasSubst b) (x : τ)
    (f : PowerSeries K) : subst b (at1 x f) = PowerSeries.subst (b x) f := by
  unfold at1
  rw [subst_psubst hb (PowerSeries.HasSubst.X x), subst_X hb]
end Formalism.InvariantFactorPaths.G7.GramFrameCompositionLinFacts
