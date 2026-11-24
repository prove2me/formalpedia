-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS.whc_rho
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:16:50.007223+00:00
-- url     : https://prove2.me/submissions/408ad2af-6160-43b1-815d-015b2b89dac5

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_GenSpaceFacts
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_GenSpace
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_GS_slc_comp
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_GS_slc_algHom
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_GS_sharp_map_rho
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_GS_dti_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_GS_torus_slice

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
theorem _root_.solution (G : MvPolynomial (LVar ι ζ n) k) (ν : Fin n → ℤ) :
    weightedHomogeneousComponent (wV isVec S) ν (rho isVec S G) = slc (prF k n ν) (rho isVec S G) := by
  rw [← torus_slice (k := k) isVec S, dti_eq]
  have := sharp_map_rho isVec S (cT k n) (dt _ n) cT_det G
  change slc _ (sharpHom isVec S _ _ (map (cT k n : UR k n →+* TR (UR k n) n) _)) = _
  rw [this, ← slc_algHom, slc_comp]
  rfl
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS
