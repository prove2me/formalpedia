-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.ScaledSeriesSubstitution.constantCoeff_zLin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:33:33.838943+00:00
-- url     : https://prove2.me/submissions/ace19c4f-8a0a-4e5c-b16a-f3c0a60f18eb

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementJ
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EJoint
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_NormLiftLeOne
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_OmegaOfTraceDuality
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EChain

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
open Formalism.DworkPowerSeriesWeights (Integral mvExp frameJet)
open Formalism.GrowthSums (gamP rhoP gainG excessGain)
open Formalism.InvariantFactorPaths.G7.ScaledSeriesSubstitution
namespace Formalism.InvariantFactorPaths.G7.ScaledSeriesSubstitution
theorem _root_.solution {K : Type} [Field K] {ν r0 r1 : ℕ} [NeZero ν]
    (om oms : Fin ν → ZMod (2 * ν) → K) (x : Bool × EV ν r0 r1) :
    MvPowerSeries.constantCoeff (zLin om oms x) = 0 := by
  unfold zLin
  rw [map_sum]
  refine Finset.sum_eq_zero fun s _ => ?_
  split_ifs <;> simp
end Formalism.InvariantFactorPaths.G7.ScaledSeriesSubstitution
