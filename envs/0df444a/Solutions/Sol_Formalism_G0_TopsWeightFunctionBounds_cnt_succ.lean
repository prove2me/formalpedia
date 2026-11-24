-- Prove2me | solution 1 for Formalism.G0.TopsWeightFunctionBounds.cnt_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:12:44.000055+00:00
-- url     : https://prove2.me/submissions/e72ddf0d-71d4-4871-9d1b-ca4ddd1e6041

import Definitions.Def_Formalism_SubspaceCounting_TopsChoiceSecondBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartB

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
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0 Formalism.G0.TopsWeightFunctionBounds
namespace Formalism.G0.TopsWeightFunctionBounds
theorem _root_.solution (n : ℕ) (T : Finset ℕ) (b t : ℕ) :
    cnt n T b (t + 1) = cnt n T b t + (if (b + (t + 1)) % n ∈ T then 1 else 0) := by
  unfold cnt
  rw [Finset.range_add_one (n := t + 1), Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem]
    simp
  · rfl
end Formalism.G0.TopsWeightFunctionBounds
