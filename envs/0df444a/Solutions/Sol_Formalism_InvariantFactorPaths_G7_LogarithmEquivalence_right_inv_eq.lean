-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.right_inv_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:27:13.486655+00:00
-- url     : https://prove2.me/submissions/d58a17f0-3fee-40e0-9128-0ae4ea68c450

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
theorem _root_.solution {R : Type} [CommRing R] {P μ Q : PowerSeries R}
    (hP : PowerSeries.constantCoeff P = 0) (hμ : PowerSeries.constantCoeff μ = 0)
    (hQ : (PowerSeries.subst P Q : PowerSeries R) = PowerSeries.X)
    (h : (PowerSeries.subst μ P : PowerSeries R) = PowerSeries.X) : μ = Q := by
  have hsP := PowerSeries.HasSubst.of_constantCoeff_zero' hP
  have hsμ := PowerSeries.HasSubst.of_constantCoeff_zero' hμ
  calc μ = PowerSeries.subst μ (PowerSeries.X : PowerSeries R) := (PowerSeries.subst_X hsμ).symm
    _ = PowerSeries.subst μ (PowerSeries.subst P Q : PowerSeries R) := by rw [hQ]
    _ = PowerSeries.subst (PowerSeries.subst μ P : PowerSeries R) Q :=
        PowerSeries.subst_comp_subst_apply hsP hsμ Q
    _ = PowerSeries.subst (PowerSeries.X : PowerSeries R) Q := by rw [h]
    _ = Q := PowerSeries.X_subst Q
end Formalism.InvariantFactorPaths.G7.LogarithmEquivalence
