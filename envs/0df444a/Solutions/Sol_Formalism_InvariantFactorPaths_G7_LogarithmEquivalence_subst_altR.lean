-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.subst_altR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:52:49.360154+00:00
-- url     : https://prove2.me/submissions/45654524-6037-4a08-8e53-6b2de3f80b47

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_CyclicPowerClassOfExpEquiv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BallRing
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_constantCoeff_altR
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_altR_add_expand
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_altR_pow

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
theorem _root_.solution (R : Type) [CommRing R] {p : ℕ} (hp : p.Prime) [CharP R p] :
    (PowerSeries.subst (altR R p) (PowerSeries.X + PowerSeries.X ^ (p ^ 2) : PowerSeries R) :
      PowerSeries R) = PowerSeries.X := by
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero' (constantCoeff_altR R hp.two_le)
  have hq : p ^ 2 ≠ 0 := pow_ne_zero 2 hp.ne_zero
  rw [PowerSeries.subst_add hs, PowerSeries.subst_pow hs, PowerSeries.subst_X hs, altR_pow R hp hq,
    altR_add_expand R hp.two_le hq]
end Formalism.InvariantFactorPaths.G7.LogarithmEquivalence
