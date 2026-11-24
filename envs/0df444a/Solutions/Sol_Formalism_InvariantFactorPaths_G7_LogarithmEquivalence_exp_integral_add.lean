-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.exp_integral_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:06:47.429744+00:00
-- url     : https://prove2.me/submissions/51a2d991-df7b-4fc0-adb1-81b229dba099

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_CyclicPowerClassOfExpEquiv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BallRing
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_integral_mul__d725f3beb1b3
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_mvExp_add


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
theorem _root_.solution {K ι : Type} [NormedField K] [IsUltrametricDist K] [CharZero K]
    {a b : MvPowerSeries ι K}
    (ha : MvPowerSeries.constantCoeff a = 0 ∧ Integral (mvExp a))
    (hb : MvPowerSeries.constantCoeff b = 0 ∧ Integral (mvExp b)) :
    MvPowerSeries.constantCoeff (a + b) = 0 ∧ Integral (mvExp (a + b)) := by
  refine ⟨by rw [map_add, ha.1, hb.1, add_zero], ?_⟩
  rw [mvExp_add ha.1 hb.1]
  exact integral_mul' ha.2 hb.2
end Formalism.InvariantFactorPaths.G7.LogarithmEquivalence
