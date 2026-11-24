-- Prove2me | solution 1 for Formalism.G0.tops_choice_count
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:22:51.098801+00:00
-- url     : https://prove2.me/submissions/8d9439ba-9e1b-4d62-a877-f64dbcff998b

import Definitions.Def_Formalism_SubspaceCounting_TopsChoiceSecondBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoiceCount
import Theorems.Thm_Formalism_G0_TopsCount_a_nonneg
import Theorems.Thm_Formalism_G0_TopsCount_binLower_eq
import Theorems.Thm_Formalism_G0_TopsCount_condProb_card

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
open TopsCount
namespace Formalism.G0
theorem _root_.solution : SmallCardCondProbBound := by
  intro n δ N hn h0 h1
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [condProb_card, binLower_eq]
  have hA : A m δ (N - 1) ≤ A m δ N := by
    unfold A
    exact sum_le_sum_of_subset_of_nonneg (range_subset_range.2 (Nat.sub_le _ _))
      (fun j _ _ => a_nonneg h0 h1 j)
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 hA)]
end Formalism.G0
