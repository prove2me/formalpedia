-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.altF_eq_altR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:05:07.664584+00:00
-- url     : https://prove2.me/submissions/bbf91878-dd9e-46f7-b668-0a9bfe5d785d

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_CyclicPowerClassOfExpEquiv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BallRing
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence

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
open Formalism.InvariantFactorPaths.G7.LogarithmEquivalence
namespace Formalism.InvariantFactorPaths.G7.LogarithmEquivalence
theorem _root_.solution (K : Type) [Field K] (p : ℕ) : altF K p = altR K p := rfl
end Formalism.InvariantFactorPaths.G7.LogarithmEquivalence
