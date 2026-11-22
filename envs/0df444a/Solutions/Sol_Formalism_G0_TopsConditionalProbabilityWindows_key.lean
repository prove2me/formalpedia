-- Prove2me | solution 1 for Formalism.G0.TopsConditionalProbabilityWindows.key
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:44:56.666407+00:00
-- url     : https://prove2.me/submissions/268ac5bc-2538-4d95-8c76-745114a22850

import Definitions.Def_Formalism_SubspaceCounting_TopsChoiceSecondBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.G0
open Formalism.G0.TopsConditionalProbabilityWindows
namespace Formalism.G0.TopsConditionalProbabilityWindows
theorem _root_.solution (n L K : ℕ) (t : Finset ℕ) (h0t : 0 ∉ t) (h : ¬ CondA n (insert 0 t) L K) :
    ∃ i ∈ range n, ∃ S ∈ powersetCard (if 0 ∈ window n i L then K else K + 1)
      ((window n i L).erase 0), S ⊆ t := by
  classical
  unfold CondA at h
  push Not at h
  obtain ⟨i, hi, hK⟩ := h
  refine ⟨i, mem_range.2 hi, ?_⟩
  set W := window n i L
  set s := t ∩ W.erase 0 with hs_def
  have hm : (if 0 ∈ W then K else K + 1) ≤ s.card := by
    by_cases hw : 0 ∈ W
    · rw [if_pos hw]
      have hsub : insert 0 t ∩ W ⊆ insert 0 s := by
        intro x hx
        rcases mem_inter.1 hx with ⟨hx1, hx2⟩
        rcases mem_insert.1 hx1 with rfl | hxt
        · exact mem_insert_self _ _
        · refine mem_insert_of_mem (mem_inter.2 ⟨hxt, mem_erase.2 ⟨?_, hx2⟩⟩)
          rintro rfl
          exact h0t hxt
      have := (card_le_card hsub).trans (card_insert_le 0 s)
      omega
    · rw [if_neg hw]
      have hsub : insert 0 t ∩ W ⊆ s := by
        intro x hx
        rcases mem_inter.1 hx with ⟨hx1, hx2⟩
        have hx0 : x ≠ 0 := by
          rintro rfl
          exact hw hx2
        rcases mem_insert.1 hx1 with hx | hxt
        · exact absurd hx hx0
        · exact mem_inter.2 ⟨hxt, mem_erase.2 ⟨hx0, hx2⟩⟩
      have := card_le_card hsub
      omega
  obtain ⟨S, hSs, hSc⟩ := exists_subset_card_eq hm
  refine ⟨S, mem_powersetCard.2 ⟨?_, hSc⟩, ?_⟩
  · exact fun x hx => (mem_inter.1 (hSs hx)).2
  · exact fun x hx => (mem_inter.1 (hSs hx)).1
end Formalism.G0.TopsConditionalProbabilityWindows
