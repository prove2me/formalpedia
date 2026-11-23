-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.subst_lgF_scale
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:32:31.967052+00:00
-- url     : https://prove2.me/submissions/1684fcec-42a9-49d5-8252-983326c9a3ec

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
    (PowerSeries.subst (PowerSeries.C ϖ * PowerSeries.X : PowerSeries K) (lgF K p) : PowerSeries K) =
      PowerSeries.C ϖ * lamF p ϖ := by
  have e : (PowerSeries.C ϖ * PowerSeries.X : PowerSeries K) = ϖ • PowerSeries.X :=
    (PowerSeries.smul_eq_C_mul _ _).symm
  rw [e, ← PowerSeries.rescale_eq_subst]
  ext n
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_C_mul, coeff_lamF]
  rcases n with _ | n
  · rw [coeff_zero_lgF]
    simp
  · rw [Nat.add_sub_cancel]
    ring
end Formalism.InvariantFactorPaths.G7.LogarithmEquivalence
