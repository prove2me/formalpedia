-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.actFormContract
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:14:15.923305+00:00
-- url     : https://prove2.me/submissions/bdc0081f-ccf7-41f3-b945-814882debdf1

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_contractWedge
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_actF_add
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_actF_smul
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_actF_sub
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_contrF_add
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_contrF_smul
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_actFormWedge
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_form_induction
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_actF_oneF
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_contrF_oneF
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_actF_zero

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
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
variable {R : Type*} [CommRing R] {n : ℕ}
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases
theorem _root_.solution : FactX2contr := by
  intro R _ n K Y g
  have hc : ∀ X : Fin n → R, ∑ a, Matrix.vecMul X (↑g : Matrix (Fin n) (Fin n) R) a *
      Matrix.vecMul Y (↑g⁻¹ : Matrix (Fin n) (Fin n) R).transpose a = ∑ a, X a * Y a := by
    intro X
    show dotProduct (Matrix.vecMul X (↑g : Matrix (Fin n) (Fin n) R))
        (Matrix.vecMul Y (↑g⁻¹ : Matrix (Fin n) (Fin n) R).transpose) = dotProduct X Y
    rw [Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Units.mul_inv,
      Matrix.one_mulVec]
  refine form_induction (P := fun K => actF (contrF K Y) (↑g : Matrix (Fin n) (Fin n) R) =
      contrF (actF K (↑g : Matrix (Fin n) (Fin n) R))
        (Matrix.vecMul Y (↑g⁻¹ : Matrix (Fin n) (Fin n) R).transpose)) ?_ ?_ ?_ ?_ K
  · try dsimp only
    rw [contrF_oneF, actF_zero, actF_oneF, contrF_oneF]
  · intro K K' h h'
    try dsimp only at h h' ⊢
    rw [contrF_add, actF_add, h, h', actF_add, contrF_add]
  · intro c K h
    try dsimp only at h ⊢
    rw [contrF_smul, actF_smul, h, actF_smul, contrF_smul]
  · intro K X h
    try dsimp only at h ⊢
    rw [contractWedge R n K X Y, actF_sub,
      show (fun I => (∑ a, X a * Y a) * K I) = (∑ a, X a * Y a) • K from rfl, actF_smul,
      actFormWedge R n (contrF K Y) X _, h, actFormWedge R n K X _,
      contractWedge R n (actF K _) (Matrix.vecMul X _) _, hc X]
    rfl
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
