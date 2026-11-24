-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.conjS_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:41:06.650915+00:00
-- url     : https://prove2.me/submissions/96d95411-719b-4608-8c62-630592da2e07

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
    conjS τ g gi last e * g.map (cc τ L) = g.map (cc τ L) * diagS (MvPolynomial τ L) n last e := by
  rw [conjS_eq, Matrix.mul_assoc, ← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _),
    Matrix.mul_one]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
