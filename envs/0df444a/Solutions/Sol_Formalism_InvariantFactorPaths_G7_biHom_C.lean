-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.biHom_C
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:15:58.748563+00:00
-- url     : https://prove2.me/submissions/a7bd02f4-e29e-437f-89fe-b0e1d4eb501c

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementAB
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BiHomSum
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DegLESum
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_FinsuppStepInduction
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_weight_one_eq

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
theorem _root_.solution {d : ℕ} {p : MvPolynomial ι K} (hp : p.IsHomogeneous d) :
    biHom d (MvPolynomial.C p : MvPolynomial κ (MvPolynomial ι K)) := by
  classical
  intro β n h
  rw [MvPolynomial.coeff_C] at h
  split_ifs at h with h1
  · have := hp h
    rw [weight_one_eq] at this
    rw [← h1, this]
    simp
  · simp at h
end Formalism.InvariantFactorPaths.G7
