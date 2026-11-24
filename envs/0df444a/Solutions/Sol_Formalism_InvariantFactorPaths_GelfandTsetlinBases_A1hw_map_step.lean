-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1hw.map_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:47:24.286031+00:00
-- url     : https://prove2.me/submissions/f3b1ada7-2dd3-4934-bfe6-888ab1b82735

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathProductHighestWeight

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
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1hw
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1hw
theorem _root_.solution {A A' : Type*} [CommRing A] [CommRing A'] (φ : A →+* A') {n : ℕ} (up : Bool)
    (K : Form A n) (K' : Form A' n) (Xv : Fin n → A) (hK : ∀ J, φ (K J) = K' J) (J : Finset (Fin n)) :
    φ (stepF up K Xv J) = stepF up K' (fun a => φ (Xv a)) J := by
  unfold stepF
  cases up
  · simp only [Bool.false_eq_true, if_false, contrF, map_sum, map_mul, map_intCast, hK]
  · simp only [if_true, wedgeF, map_sum, map_mul, map_intCast, hK]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1hw
