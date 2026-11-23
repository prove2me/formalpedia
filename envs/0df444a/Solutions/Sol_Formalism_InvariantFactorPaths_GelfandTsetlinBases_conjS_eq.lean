-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.conjS_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:57:49.900246+00:00
-- url     : https://prove2.me/submissions/fd836f5f-3430-4276-b108-bdf477bb305a

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
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases
theorem _root_.solution (τ : Type*) (g gi : Matrix (Fin n) (Fin n) L) (last : Bool) (e : ℤ) :
    conjS τ g gi last e = g.map (cc τ L) * diagS (MvPolynomial τ L) n last e * gi.map (cc τ L) := rfl
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
