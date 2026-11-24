-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.pderiv_shiftGen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:38:42.511695+00:00
-- url     : https://prove2.me/submissions/38f1aff8-8ac9-4ded-827a-ad8c1b764494

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
theorem _root_.solution (b : κ → ι → K) (x : ι) (k : κ) :
    MvPolynomial.pderiv k (shiftGen b x) = MvPolynomial.C (MvPolynomial.C (b k x)) := by
  classical
  unfold shiftGen
  rw [map_add, MvPolynomial.pderiv_C, zero_add, map_sum, Finset.sum_eq_single k]
  · rw [MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_X_self, mul_one]
  · intro k' _ hk'
    rw [MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_X_of_ne hk', mul_zero]
  · intro h
    exact absurd (Finset.mem_univ k) h
end Formalism.InvariantFactorPaths.G7
