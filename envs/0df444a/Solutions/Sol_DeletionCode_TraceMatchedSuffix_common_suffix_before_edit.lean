-- Prove2me | solution 1 for DeletionCode.TraceMatchedSuffix.common_suffix_before_edit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:49:55.915294+00:00
-- url     : https://prove2.me/submissions/0976e831-fed3-4287-a4a5-4b6b90f3f249

import Definitions.Def_DeletionCode_TraceSeparation
import Definitions.Def_DeletionCode_TraceMatchedSuffix
import Theorems.Thm_DeletionCode_TraceMatchedSuffix_matchedAnchor_le_index
import Theorems.Thm_DeletionCode_TraceMatchedSuffix_matchedAnchor_gap_le
import Theorems.Thm_DeletionCode_TraceMatchedSuffix_common_suffix_of_matched_range

set_option autoImplicit true
open DeletionCode DeletionCode.TraceMatchedSuffix
open AlignmentTrace FiniteConflictGraph TraceSeparation
namespace DeletionCode.TraceMatchedSuffix
theorem _root_.solution {trace : Trace} {L : ℕ} (hL : 1 ≤ L)
    (hsep : Separated (4 * L) trace) (i : Fin trace.length) (hi : EditIndex trace i) :
    ∃ a b common : List Bool,
      Trace.source (trace.take i.val) = a ++ common ∧
      Trace.target (trace.take i.val) = b ++ common ∧ L - 1 ≤ common.length := by
  have hanchor := (hsep.1 i hi).1
  have hindex := matchedAnchor_le_index trace i.val
  have hm : L - 1 ≤ i.val := by omega
  have hno : ∀ j : Fin trace.length,
      i.val - (L - 1) ≤ j.val → j.val < i.val → ¬ EditIndex trace j := by
    intro j hjlow hjbefore hj
    have hgap := hsep.2 j i hj hi hjbefore
    have hsmall := matchedAnchor_gap_le trace j.val i.val (Nat.le_of_lt hjbefore)
    omega
  obtain ⟨a, b, common, hs, ht, hlen⟩ := common_suffix_of_matched_range trace i.val (L - 1)
    hm (Nat.le_of_lt i.isLt) hno
  exact ⟨a, b, common, hs, ht, by omega⟩
end DeletionCode.TraceMatchedSuffix
