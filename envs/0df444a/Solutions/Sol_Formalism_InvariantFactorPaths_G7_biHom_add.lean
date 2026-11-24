-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.biHom_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:45:53.065833+00:00
-- url     : https://prove2.me/submissions/cbbb3078-7b20-46f9-a3b7-a5cff69ada8d

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementAB
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BiHomSum
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DegLESum
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_FinsuppStepInduction

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
variable {K ι κ : Type} [Field K] [Fintype κ]
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution {d : ℕ} {F G : MvPolynomial κ (MvPolynomial ι K)} (hF : biHom d F)
    (hG : biHom d G) : biHom d (F + G) := by
  intro β n h
  rw [MvPolynomial.coeff_add, MvPolynomial.coeff_add] at h
  by_cases h1 : MvPolynomial.coeff n (MvPolynomial.coeff β F) = 0
  · rw [h1, zero_add] at h
    exact hG β n h
  · exact hF β n h1
end Formalism.InvariantFactorPaths.G7
