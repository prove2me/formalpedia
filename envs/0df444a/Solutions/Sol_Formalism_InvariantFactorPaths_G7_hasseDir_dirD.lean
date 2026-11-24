-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.hasseDir_dirD
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:53:18.299805+00:00
-- url     : https://prove2.me/submissions/e800a89c-8b3a-4122-b14e-6b0541c04417

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementAB
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BiHomSum
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DegLESum
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_FinsuppStepInduction
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_shiftPoly_dirD

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
theorem _root_.solution [Fintype ι] (b : κ → ι → K) (k : κ) (β : κ →₀ ℕ) (Q : MvPolynomial ι K) :
    hasseDir b β (dirD (b k) Q) =
      MvPolynomial.C ((β k + 1 : ℕ) : K) * hasseDir b (β + Finsupp.single k 1) Q := by
  unfold hasseDir
  rw [shiftPoly_dirD, MvPolynomial.coeff_pderiv]
  simp [mul_comm]
end Formalism.InvariantFactorPaths.G7
