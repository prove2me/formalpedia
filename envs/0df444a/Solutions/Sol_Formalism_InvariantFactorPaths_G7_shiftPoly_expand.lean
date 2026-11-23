-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.shiftPoly_expand
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:06:33.357348+00:00
-- url     : https://prove2.me/submissions/aaaab401-2d4b-40f6-ad10-85aa956b5ad9

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementAB
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BiHomSum
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DegLESum
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_FinsuppStepInduction
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_shiftPoly_eq

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
theorem _root_.solution (b : κ → ι → K) (Q : MvPolynomial ι K) :
    shiftPoly b Q = ∑ d ∈ Q.support, MvPolynomial.C (MvPolynomial.C (MvPolynomial.coeff d Q)) *
      ∏ i ∈ d.support, shiftGen b i ^ d i := by
  rw [shiftPoly_eq, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  rfl
end Formalism.InvariantFactorPaths.G7
