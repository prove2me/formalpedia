-- Prove2me | solution 1 for Formalism.G0.TopsCount.pascal_term
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:12:42.97468+00:00
-- url     : https://prove2.me/submissions/8d205d7e-9037-4b44-aa34-82a905457af5

import Definitions.Def_Formalism_SubspaceCounting_TopsChoiceSecondBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoiceCount

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
open Formalism Formalism.G0
open Formalism.G0.TopsCount
namespace Formalism.G0.TopsCount
theorem _root_.solution (m k : ℕ) (δ : ℝ) :
    ((m + 1).choose (k + 1) : ℝ) * δ ^ (k + 1) * (1 - δ) ^ (m + 1 - (k + 1)) =
      (1 - δ) * a m δ (k + 1) + δ * a m δ k := by
  unfold a
  rw [Nat.choose_succ_succ', Nat.cast_add]
  have e1 : m + 1 - (k + 1) = m - k := by omega
  rw [e1]
  rcases Nat.lt_or_ge k m with hk | hk
  · have e2 : m - k = (m - (k + 1)) + 1 := by omega
    rw [e2]; ring
  · rw [Nat.choose_eq_zero_of_lt (by omega : m < k + 1)]
    push_cast; ring
end Formalism.G0.TopsCount
