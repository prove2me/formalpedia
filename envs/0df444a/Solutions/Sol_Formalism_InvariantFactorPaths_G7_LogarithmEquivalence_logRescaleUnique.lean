-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.logRescaleUnique
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:35:01.937189+00:00
-- url     : https://prove2.me/submissions/59dd812c-7519-4b82-918d-d54d8f8a1ebe

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_CyclicPowerClassOfExpEquiv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BallRing
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_right_inv_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_constantCoeff_lamF
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_coeff_one_lamF

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
theorem _root_.solution : LogRescaleUnique := by
  intro K _ p ϖ μ μ' hp _ h0 h0' h h'
  have hc := constantCoeff_lamF p ϖ
  have hu : IsUnit (PowerSeries.coeff 1 (lamF p ϖ)) := by
    rw [coeff_one_lamF hp]
    exact isUnit_one
  have hQ := PowerSeries.subst_substInvOfIsUnit_left (lamF p ϖ) hc hu
  rw [right_inv_eq hc h0 hQ h, right_inv_eq hc h0' hQ h']
end Formalism.InvariantFactorPaths.G7.LogarithmEquivalence
