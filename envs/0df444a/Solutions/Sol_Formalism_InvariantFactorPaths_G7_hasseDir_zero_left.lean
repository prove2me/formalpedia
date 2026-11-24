-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.hasseDir_zero_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:36:25.338988+00:00
-- url     : https://prove2.me/submissions/8d902d6d-6b74-443e-b0bb-29c86b18f272

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementAB
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BiHomSum
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DegLESum
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_FinsuppStepInduction
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_shiftPoly_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_shiftPoly_add
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_shiftPoly_X
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_shiftPoly_C
import Theorems.Thm_Formalism_FG_InjVAux_HasOrd_add
import Theorems.Thm_Formalism_FG_InvIntVAux_Low_add


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
theorem _root_.solution (b : κ → ι → K) (Q : MvPolynomial ι K) : hasseDir b 0 Q = Q := by
  unfold hasseDir
  rw [← MvPolynomial.constantCoeff_eq]
  induction Q using MvPolynomial.induction_on with
  | C a => rw [shiftPoly_C, MvPolynomial.constantCoeff_C]
  | add p q hp hq => rw [shiftPoly_add, map_add, hp, hq]
  | mul_X p x hp =>
    rw [shiftPoly_mul, map_mul, hp, shiftPoly_X]
    simp [shiftGen]
end Formalism.InvariantFactorPaths.G7
