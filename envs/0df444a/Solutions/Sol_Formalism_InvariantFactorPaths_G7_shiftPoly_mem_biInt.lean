-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.shiftPoly_mem_biInt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:53:10.296101+00:00
-- url     : https://prove2.me/submissions/be0af6b8-2f5b-4382-8377-58e036f2a349

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementAB
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BiHomSum
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DegLESum
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_FinsuppStepInduction
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_shiftPoly_expand
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_C_mem_biInt
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_X_mem_biInt
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_C_mem_opInt
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_X_mem_opInt

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
variable (K ι κ : Type) [NormedField K] [IsUltrametricDist K]
variable {K ι κ}
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution [Fintype κ] (b : κ → ι → K) (Q : MvPolynomial ι K)
    (hQ : ∀ n, ‖MvPolynomial.coeff n Q‖ ≤ 1) (hb : ∀ k x, ‖b k x‖ ≤ 1) :
    shiftPoly b Q ∈ biInt K ι κ := by
  rw [shiftPoly_expand]
  refine Subring.sum_mem _ fun n _ => Subring.mul_mem _ (C_mem_biInt (C_mem_opInt (hQ n)))
    (Subring.prod_mem _ fun x _ => Subring.pow_mem _ ?_ _)
  unfold shiftGen
  exact Subring.add_mem _ (C_mem_biInt (X_mem_opInt x)) (Subring.sum_mem _ fun k _ =>
    Subring.mul_mem _ (C_mem_biInt (C_mem_opInt (hb k x))) (X_mem_biInt k))
end Formalism.InvariantFactorPaths.G7
