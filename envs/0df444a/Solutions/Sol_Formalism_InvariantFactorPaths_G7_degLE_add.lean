-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.degLE_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:27:54.630022+00:00
-- url     : https://prove2.me/submissions/1a9fb578-0b4b-4879-96a1-28d8792a8f61

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
variable {κ R : Type} [CommRing R]
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution {W : Finset κ} {n : ℕ} {F G : MvPolynomial κ R} (hF : degLE W n F)
    (hG : degLE W n G) : degLE W n (F + G) := by
  intro β h
  rw [MvPolynomial.coeff_add] at h
  by_cases h1 : MvPolynomial.coeff β F = 0
  · rw [h1, zero_add] at h
    exact hG β h
  · exact hF β h1
end Formalism.InvariantFactorPaths.G7
