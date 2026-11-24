-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.hasseDir_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:36:25.137854+00:00
-- url     : https://prove2.me/submissions/a6f9af42-4418-46d2-b74a-bc2ed67879ea

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementAB
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BiHomSum
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DegLESum
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_FinsuppStepInduction
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_shiftPoly_mul

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
theorem _root_.solution [DecidableEq κ] (b : κ → ι → K) (β : κ →₀ ℕ) (f g : MvPolynomial ι K) :
    hasseDir b β (f * g) =
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal β, hasseDir b x.1 f * hasseDir b x.2 g := by
  simp only [hasseDir, shiftPoly_mul, MvPolynomial.coeff_mul]
end Formalism.InvariantFactorPaths.G7
