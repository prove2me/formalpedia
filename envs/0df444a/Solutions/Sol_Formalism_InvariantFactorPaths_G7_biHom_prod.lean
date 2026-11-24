-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.biHom_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:14:27.590022+00:00
-- url     : https://prove2.me/submissions/9db40c29-0566-4c5f-9872-bc9b8b96e772

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementAB
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BiHomSum
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DegLESum
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_FinsuppStepInduction
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_biHom_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_biHom_one

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
theorem _root_.solution {α : Type*} (s : Finset α) (d : α → ℕ)
    (F : α → MvPolynomial κ (MvPolynomial ι K)) (h : ∀ a ∈ s, biHom (d a) (F a)) :
    biHom (∑ a ∈ s, d a) (∏ a ∈ s, F a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using biHom_one
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact biHom_mul (h a (Finset.mem_insert_self _ _))
      (ih fun a' ha' => h a' (Finset.mem_insert_of_mem ha'))
end Formalism.InvariantFactorPaths.G7
