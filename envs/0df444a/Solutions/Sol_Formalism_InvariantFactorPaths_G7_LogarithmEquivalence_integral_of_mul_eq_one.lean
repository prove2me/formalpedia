-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_of_mul_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:31:57.264797+00:00
-- url     : https://prove2.me/submissions/d33a6aff-dc14-4360-a2a5-2db9a61ec5ce

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_CyclicPowerClassOfExpEquiv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BallRing
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_integral_iff_lift
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_constantCoeff_lift

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
theorem _root_.solution {K ι : Type} [NormedField K] [IsUltrametricDist K]
    {u v : MvPowerSeries ι K} (hu : Integral u) (h1 : MvPowerSeries.constantCoeff u = 1)
    (huv : v * u = 1) : Integral v := by
  obtain ⟨u₀, rfl⟩ := integral_iff_lift.1 hu
  have hc : MvPowerSeries.constantCoeff u₀ = 1 := constantCoeff_lift (c := 1) (by rw [h1]; rfl)
  have hU : IsUnit u₀ := MvPowerSeries.isUnit_iff_constantCoeff.2 (by rw [hc]; exact isUnit_one)
  obtain ⟨w, hw⟩ := hU.exists_right_inv
  have e : v = MvPowerSeries.map (ballRing K).subtype w := by
    calc v = v * (MvPowerSeries.map (ballRing K).subtype u₀ *
          MvPowerSeries.map (ballRing K).subtype w) := by rw [← map_mul, hw, map_one, mul_one]
      _ = MvPowerSeries.map (ballRing K).subtype w := by rw [← mul_assoc, huv, one_mul]
  rw [e]
  exact integral_iff_lift.2 ⟨w, rfl⟩
end Formalism.InvariantFactorPaths.G7.LogarithmEquivalence
