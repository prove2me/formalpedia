-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.degLE_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:49:24.013799+00:00
-- url     : https://prove2.me/submissions/5d0179bd-09aa-4f59-8aa9-6b1952e4be52

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementAB
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BiHomSum
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DegLESum
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_FinsuppStepInduction
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_degLE_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_degLE_one

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
theorem _root_.solution {α : Type*} {W : Finset κ} (s : Finset α) (n : α → ℕ)
    (F : α → MvPolynomial κ R) (h : ∀ a ∈ s, degLE W (n a) (F a)) :
    degLE W (∑ a ∈ s, n a) (∏ a ∈ s, F a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using degLE_one W
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact degLE_mul (h a (Finset.mem_insert_self _ _))
      (ih fun a' ha' => h a' (Finset.mem_insert_of_mem ha'))
end Formalism.InvariantFactorPaths.G7
