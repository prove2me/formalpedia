-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.constantCoeff_lamF
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:32:15.722261+00:00
-- url     : https://prove2.me/submissions/7549072b-fa6c-41a6-99cc-38684c3f18e6

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_CyclicPowerClassOfExpEquiv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BallRing
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_coeff_lamF
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_coeff_zero_lgF

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
theorem _root_.solution {K : Type} [Field K] (p : ℕ) (ϖ : K) :
    PowerSeries.constantCoeff (lamF p ϖ) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_lamF, coeff_zero_lgF, mul_zero]
end Formalism.InvariantFactorPaths.G7.LogarithmEquivalence
