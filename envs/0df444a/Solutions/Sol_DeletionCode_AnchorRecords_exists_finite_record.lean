-- Prove2me | solution 1 for DeletionCode.AnchorRecords.exists_finite_record
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:01:55.960595+00:00
-- url     : https://prove2.me/submissions/0fa573b6-b9f3-4d74-a755-b70a1ea1888e

import Definitions.Def_DeletionCode_TraceEditData
import Definitions.Def_DeletionCode_TraceSeparation
import Mathlib.Data.List.OfFn
import Definitions.Def_DeletionCode_AnchorRecords
import Theorems.Thm_DeletionCode_AnchorRecords_encode_length
import Theorems.Thm_DeletionCode_AnchorRecords_encode_anchor_lt_source
import Theorems.Thm_DeletionCode_AnchorRecords_finite_record_of_bounds

set_option autoImplicit true
open DeletionCode DeletionCode.AnchorRecords
open AlignmentTrace TraceEditData
namespace DeletionCode.AnchorRecords
theorem _root_.solution (trace : Trace) (n d : ℕ)
    (hsource : trace.source.length = n) (hdel : trace.deletions = d)
    (hins : trace.insertions = d) (hd : 1 ≤ d) :
    ∃ anchors : Fin (2 * d) → Fin n, ∃ data : Fin (2 * d) → Bool × Bool,
      List.ofFn (fun i => ((anchors i).val, data i)) = encode trace := by
  apply finite_record_of_bounds
  · rw [encode_length, hdel, hins]
    omega
  · intro p hp
    rw [← hsource]
    exact encode_anchor_lt_source trace (by omega) p hp
end DeletionCode.AnchorRecords
