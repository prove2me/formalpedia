-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.biHom_shiftGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:10:37.764024+00:00
-- url     : https://prove2.me/submissions/fb3b7979-8628-4ac7-bdc4-a8721a93e48a

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementAB
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BiHomSum
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DegLESum
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_FinsuppStepInduction
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_biHom_add
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_biHom_sum
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_biHom_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_biHom_C
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_biHom_X

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
theorem _root_.solution (b : κ → ι → K) (x : ι) : biHom 1 (shiftGen b x) := by
  unfold shiftGen
  refine biHom_add (biHom_C (MvPolynomial.isHomogeneous_X K x)) (biHom_sum _ _ fun k _ => ?_)
  have := biHom_mul (biHom_C (κ := κ) (MvPolynomial.isHomogeneous_C ι (b k x)))
    (biHom_X (ι := ι) (K := K) k)
  simpa using this
end Formalism.InvariantFactorPaths.G7
