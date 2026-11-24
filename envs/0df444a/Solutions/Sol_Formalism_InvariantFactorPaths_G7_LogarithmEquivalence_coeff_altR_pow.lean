-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.coeff_altR_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:06:47.418564+00:00
-- url     : https://prove2.me/submissions/46da5650-8c47-4047-bfa0-a80f6d726803

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_CyclicPowerClassOfExpEquiv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BallRing
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_lt_powq
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_powq_inj
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_sum_range_ite_unique


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
theorem _root_.solution (R : Type) [CommRing R] {p : ℕ} (hp : 2 ≤ p) (l : ℕ) :
    PowerSeries.coeff ((p ^ 2) ^ l) (altR R p) = (-1) ^ l := by
  unfold altR
  rw [PowerSeries.coeff_mk]
  exact sum_range_ite_unique _ (fun l' => (p ^ 2) ^ l = (p ^ 2) ^ l') _ l (lt_powq hp l) rfl
    fun l' h => (powq_inj hp h).symm
end Formalism.InvariantFactorPaths.G7.LogarithmEquivalence
