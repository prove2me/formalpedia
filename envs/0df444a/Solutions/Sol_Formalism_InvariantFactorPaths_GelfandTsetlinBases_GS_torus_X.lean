-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS.torus_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:47:54.655847+00:00
-- url     : https://prove2.me/submissions/f060553b-48eb-4020-b3d0-36295d291154

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_GenSpaceFacts
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_GenSpace
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_GS_sharp_vec
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_GS_sharp_covec
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_GS_sharp_out
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_GS_sharp_further

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
theorem _root_.solution (x : LVar ι ζ n) :
    sharpHom isVec S (dt A n) (dti A n) (X x) = C (AddMonoidAlgebra.single (wV isVec S x) 1) * X x := by
  classical
  rcases x with ⟨i, a⟩ | z
  · by_cases h1 : i ∈ S
    · cases h3 : isVec i
      · rw [sharp_covec h1 h3]
        simp [dti, Matrix.diagonal_apply, wV, h1, h3, mul_comm, apply_ite C]
      · rw [sharp_vec h1 h3]
        simp [dt, Matrix.diagonal_apply, wV, h1, h3, mul_comm, apply_ite C]
    · rw [sharp_out h1]
      simp [wV, h1, ← AddMonoidAlgebra.one_def]
  · rw [sharp_further]
    simp [wV, ← AddMonoidAlgebra.one_def]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS
