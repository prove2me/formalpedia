-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.conjAct_C
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:40:37.631152+00:00
-- url     : https://prove2.me/submissions/276f1265-c658-4751-a4b9-a8a9a559cd85

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe

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
variable (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases
theorem _root_.solution {k : Type*} [CommRing k] (φ : k →+* L) (g gi : Matrix (Fin n) (Fin n) L) (last : Bool) (c : k) :
    conjAct (ζ := ζ) φ isVec S g gi last (C c) = cc _ L (φ c) := by
  simp [conjAct]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
