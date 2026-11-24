-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.e_one_integral_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:32:57.494529+00:00
-- url     : https://prove2.me/submissions/4aebde70-1a04-43c8-a716-d3da67ed0fbf

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementAB
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BiHomSum
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DegLESum
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_FinsuppStepInduction
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_weight_one_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_biHom_shiftPoly
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_shiftPoly_mem_biInt

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
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution : HasseDerivIntegralHomogeneous := by
  intro K ι κ _ _ _ b β Q
  refine ⟨fun hQ hb n => shiftPoly_mem_biInt b Q hQ hb β n, fun d hQ => ?_, fun d hQ hd => ?_⟩
  · intro n hn
    have := biHom_shiftPoly b hQ β n hn
    rw [Finsupp.degree_eq_sum β] at this
    rw [weight_one_eq]
    omega
  · ext n
    by_contra hn
    have := biHom_shiftPoly b hQ β n hn
    rw [Finsupp.degree_eq_sum β] at this
    omega
end Formalism.InvariantFactorPaths.G7
