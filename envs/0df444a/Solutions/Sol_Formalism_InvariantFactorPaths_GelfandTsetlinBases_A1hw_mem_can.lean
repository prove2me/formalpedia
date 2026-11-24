-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1hw.mem_can
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:47:25.415365+00:00
-- url     : https://prove2.me/submissions/df1194f5-9dc0-4a7f-9c48-801e18f3f555

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathProductHighestWeight
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Paths_le_iff_lt_colHeight


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
theorem _root_.solution {n : ℕ} {μN : Fin n → ℤ} (h : Antitone μN) (c : ℤ) (m : Fin n) :
    m ∈ canIdx μN c ↔ if 1 ≤ c then c ≤ μN m else μN m < c := by
  unfold canIdx
  split_ifs with hc
  · simp only [mem_filter, mem_univ, true_and]
    exact (Paths.le_iff_lt_colHeight h c m).symm
  · simp only [mem_filter, mem_univ, true_and]
    rw [← not_le, Paths.le_iff_lt_colHeight h c m, not_lt]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1hw
