-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.A0.gH_in
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:46:34.511642+00:00
-- url     : https://prove2.me/submissions/0110f91b-10c8-4fe1-807a-291215f2807d

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_ValuationProductsComponents
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathProductHighestWeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ValuationProductsComponents
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A0_gam_val
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A0_gam_inv

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
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.A0
variable (k : Type) [Field k] {n : ℕ} (isVec : ℕ → Bool) (S : Set ℕ) [DecidablePred (· ∈ S)]
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.A0
theorem _root_.solution {j : ℕ} (hj : j ∈ S) :
    (fun a : Fin n => gH k isVec S (X (j, a))) =
      if isVec j then
        Matrix.vecMul (fun b => (X (Sum.inl (j, b)) : MvPolynomial (LVar ℕ Empty n) (GenField k n)))
          (↑(gam k n (LVar ℕ Empty n)) : Matrix (Fin n) (Fin n) _)
      else
        Matrix.vecMul (fun b => (X (Sum.inl (j, b)) : MvPolynomial (LVar ℕ Empty n) (GenField k n)))
          (↑(gam k n (LVar ℕ Empty n))⁻¹ : Matrix (Fin n) (Fin n) _).transpose := by
  funext a
  rw [gam_val, gam_inv]
  have h : gH k isVec S (X (j, a)) =
      sharpHom isVec S (genMat k n)⁻¹ (genMat k n) (X (Sum.inl (j, a))) := by
    simp [gH]
  rw [h]
  cases hv : isVec j
  · simp [sharpHom, hj, hv]
  · simp [sharpHom, hj, hv]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.A0
