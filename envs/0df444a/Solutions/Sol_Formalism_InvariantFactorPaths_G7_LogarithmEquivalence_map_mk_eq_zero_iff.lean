-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.map_mk_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:45:52.334025+00:00
-- url     : https://prove2.me/submissions/25897377-4dfd-4022-a12b-4e2aea909018

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_CyclicPowerClassOfExpEquiv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BallRing
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_mem_span_p_iff

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
theorem _root_.solution {K : Type} [NormedField K] [IsUltrametricDist K] {p : ℕ} (hp : p.Prime)
    (hn : ‖(p : K)‖ = (p : ℝ)⁻¹) (f : PowerSeries (ballRing K)) :
    PowerSeries.map (Ideal.Quotient.mk (Ideal.span {(p : ballRing K)})) f = 0 ↔
      ∀ n, ‖PowerSeries.coeff n (PowerSeries.map (ballRing K).subtype f)‖ ≤ (p : ℝ)⁻¹ := by
  rw [PowerSeries.ext_iff]
  refine forall_congr' fun n => ?_
  rw [PowerSeries.coeff_map, PowerSeries.coeff_map, map_zero, Ideal.Quotient.eq_zero_iff_mem,
    mem_span_p_iff hp hn]
  rfl
end Formalism.InvariantFactorPaths.G7.LogarithmEquivalence
