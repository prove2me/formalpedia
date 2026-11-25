-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1.mem_canIdx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:06:22.467522+00:00
-- url     : https://prove2.me/submissions/8474152f-0231-49c8-9e53-85be96665563

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
theorem _root_.solution {n : ℕ} (μN : Fin n → ℤ) (c : ℤ) (m : Fin n) :
    m ∈ canIdx μN c ↔ if 1 ≤ c then m.val < colHeight μN c else colHeight μN c ≤ m.val := by
  unfold Formalism.InvariantFactorPaths.GelfandTsetlinBases.canIdx
  split_ifs <;> simp
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1
