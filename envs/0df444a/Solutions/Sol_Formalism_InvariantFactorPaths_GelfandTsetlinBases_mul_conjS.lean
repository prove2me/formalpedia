-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.mul_conjS
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:01:14.195685+00:00
-- url     : https://prove2.me/submissions/6b7545de-a857-4dd9-ac19-f21dea512bec

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_conjS_eq

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
variable {ι ζ : Type*} {n : ℕ} {L : Type*} [CommRing L]
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases
theorem _root_.solution (τ : Type*) {g gi : Matrix (Fin n) (Fin n) L} (h : gi * g = 1) (last : Bool) (e : ℤ) :
    gi.map (cc τ L) * conjS τ g gi last e = diagS (MvPolynomial τ L) n last e * gi.map (cc τ L) := by
  rw [conjS_eq, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.map_mul, h,
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
