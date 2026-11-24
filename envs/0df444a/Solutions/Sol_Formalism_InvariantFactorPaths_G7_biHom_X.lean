-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.biHom_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:45:50.931748+00:00
-- url     : https://prove2.me/submissions/7e3bc792-71ac-41d8-ae12-9fc7a7e7c557

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
theorem _root_.solution (k : κ) : biHom 1 (MvPolynomial.X k : MvPolynomial κ (MvPolynomial ι K)) := by
  classical
  intro β n h
  rw [MvPolynomial.coeff_X] at h
  split_ifs at h with h1
  · rw [MvPolynomial.coeff_one] at h
    split_ifs at h with h2
    · rw [← h1, ← h2]
      simp
    · exact absurd rfl h
  · simp at h
end Formalism.InvariantFactorPaths.G7
