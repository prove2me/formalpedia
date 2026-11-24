-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.altR_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:06:47.531683+00:00
-- url     : https://prove2.me/submissions/46ab1bce-76e8-4323-9ae4-ac101652dac7

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_CyclicPowerClassOfExpEquiv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BallRing
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_map_altR

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
theorem _root_.solution (R : Type) [CommRing R] {p : ℕ} (hp : p.Prime) [CharP R p] (hq : p ^ 2 ≠ 0) :
    altR R p ^ (p ^ 2) = PowerSeries.expand (p ^ 2) hq (altR R p) := by
  have : ExpChar R p := ExpChar.prime hp
  have h := MvPowerSeries.map_iterateFrobenius_expand (σ := Unit) p hp.ne_zero (altR R p) 2
  refine h.symm.trans ?_
  change PowerSeries.map (iterateFrobenius R p 2) (PowerSeries.expand (p ^ 2) hq (altR R p)) = _
  rw [PowerSeries.map_expand, map_altR]
end Formalism.InvariantFactorPaths.G7.LogarithmEquivalence
