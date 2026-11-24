-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS.sharp_map_rho
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:53:50.409549+00:00
-- url     : https://prove2.me/submissions/bf7673ca-c91e-48f9-8b7a-bf28a30cec14

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_GenSpaceFacts
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_GenSpace
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_GS_sharp_nat
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_GS_sharp_comp
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_GS_map_nonsing_inv
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_GS_act_eq

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
variable {k : Type*} [Field k] {ι ζ : Type*} {n : ℕ} (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS
theorem _root_.solution {B : Type*} [CommRing B] [Algebra k B] (c : UR k n →ₐ[k] B)
    (x : Matrix (Fin n) (Fin n) B) (hxy : IsUnit (x * (uMat k n).map (c : UR k n →+* B)).det)
    (G : MvPolynomial (LVar ι ζ n) k) :
    sharpHom isVec S x x⁻¹ (map (c : UR k n →+* B) (rho isVec S G)) =
      map (uAlg k (x * (uMat k n).map (c : UR k n →+* B)) hxy : UR k n →+* B) (rho isVec S G) := by
  rw [← act_eq, Matrix.mul_inv_rev, ← map_nonsing_inv _ _ (uMat_det k n), ← sharp_comp, rho, sharp_nat, MvPolynomial.map_map,
    AlgHom.comp_algebraMap]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS
