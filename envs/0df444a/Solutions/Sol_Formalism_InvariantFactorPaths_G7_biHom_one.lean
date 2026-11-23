-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.biHom_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:15:58.899189+00:00
-- url     : https://prove2.me/submissions/1435895b-e33e-4e07-bac3-f71047384da7

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
theorem _root_.solution : biHom 0 (1 : MvPolynomial κ (MvPolynomial ι K)) := by
  classical
  intro β n h
  rw [MvPolynomial.coeff_one] at h
  split_ifs at h with h1
  · rw [MvPolynomial.coeff_one] at h
    split_ifs at h with h2
    · rw [← h1, ← h2]
      simp
    · exact absurd rfl h
  · simp at h
end Formalism.InvariantFactorPaths.G7
