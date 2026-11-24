-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS.prod_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:47:20.757924+00:00
-- url     : https://prove2.me/submissions/a09a3721-5d66-4613-a2e7-d5313ee3da51

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_GenSpaceFacts
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_GenSpace

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
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS
variable {ι ζ : Type*} {n : ℕ} (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]
variable (A : Type*) [CommRing A]
variable {A}
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS
theorem _root_.solution {κ M : Type*} [AddCommMonoid M] (s : Finset κ) (f : κ → M) :
    ∏ x ∈ s, (AddMonoidAlgebra.single (f x) (1 : A) : AddMonoidAlgebra A M) =
      AddMonoidAlgebra.single (∑ x ∈ s, f x) 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [AddMonoidAlgebra.one_def]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, AddMonoidAlgebra.single_mul_single, mul_one]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS
