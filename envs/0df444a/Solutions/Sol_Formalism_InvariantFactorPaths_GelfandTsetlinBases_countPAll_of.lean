-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.countPAll_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:52:21.446598+00:00
-- url     : https://prove2.me/submissions/330f06b7-f121-4835-ade0-6426f1a73041

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementP
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_NormIndexCountBound
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Count_dGT_zero

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
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases
theorem _root_.solution : CountCont → CountPAll := by
  intro hCC n N isVec B
  unfold CountP
  obtain ⟨-, hcard⟩ := hCC n 0 N isVec B 0 (Nat.zero_le N) (fun _ _ _ => le_rfl)
  rw [Nat.card_congr (Count.pathEquiv n N isVec B), hcard, Count.dGT_zero, one_mul, Finset.range_eq_Ico]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
