-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.jetPair_linS_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:53:48.268536+00:00
-- url     : https://prove2.me/submissions/da998fba-1cf5-45e6-ae86-1c3219070c69

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementAB
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BiHomSum
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DegLESum
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_FinsuppStepInduction
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_jetPair_X_mul
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_C_mul_left
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_C_mul_right
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_sum_left
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_sum_right


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
open Formalism.DworkPowerSeriesWeights (jetPair)
variable {K ι : Type} [Field K]
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution [Fintype ι] (c : ι → K) (Q : MvPolynomial ι K) (G : MvPowerSeries ι K) :
    jetPair Q (linS c * G) = jetPair (dirD c Q) G := by
  unfold linS dirD
  rw [Finset.sum_mul, Formalism.DworkPowerSeriesWeights.jetPair_sum_right, Formalism.DworkPowerSeriesWeights.jetPair_sum_left]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [mul_assoc, Formalism.DworkPowerSeriesWeights.jetPair_C_mul_right, Formalism.DworkPowerSeriesWeights.jetPair_C_mul_left, jetPair_X_mul]
end Formalism.InvariantFactorPaths.G7
