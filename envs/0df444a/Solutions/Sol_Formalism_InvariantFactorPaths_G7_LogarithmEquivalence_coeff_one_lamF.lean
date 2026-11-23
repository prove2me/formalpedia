-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.coeff_one_lamF
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:31:27.327731+00:00
-- url     : https://prove2.me/submissions/bc11aaea-b487-4066-a142-087b1b1a0b39

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_CyclicPowerClassOfExpEquiv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BallRing
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_coeff_lamF
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_lgF_pow


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
theorem _root_.solution {K : Type} [Field K] {p : ℕ} (hp : 2 ≤ p) (ϖ : K) :
    PowerSeries.coeff 1 (lamF p ϖ) = 1 := by
  have h := coeff_lgF_pow K hp 0
  rw [pow_zero, pow_zero, inv_one] at h
  rw [coeff_lamF, h]
  simp
end Formalism.InvariantFactorPaths.G7.LogarithmEquivalence
