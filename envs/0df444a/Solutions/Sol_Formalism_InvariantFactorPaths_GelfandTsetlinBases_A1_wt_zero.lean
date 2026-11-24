-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1.wt_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:47:22.145786+00:00
-- url     : https://prove2.me/submissions/634a6310-aff9-46e8-8ff9-8ac4bd86f62e

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IsWeightedHomogeneousZeroStripPathWord

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
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1
theorem _root_.solution {n N : ℕ} (v : Bool) {x : ℕ × Fin n} (hx : x.1 ≠ N) : wt n N v x = 0 := by
  have h : ∀ j : Fin n, (Finsupp.single x 1 : ℕ × Fin n →₀ ℕ) (N, rw_ v j) = 0 := fun j => by
    rw [Finsupp.single_apply, if_neg]
    rintro rfl
    exact hx rfl
  show toLex (fun j => (Finsupp.single x 1 : ℕ × Fin n →₀ ℕ) (N, rw_ v j)) = 0
  simp only [h]
  rfl
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1
