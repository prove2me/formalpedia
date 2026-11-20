-- Prove2me | solution 1 for DeletionCode.AnchorRecords.vector_edit_indices
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:04:03.721113+00:00
-- url     : https://prove2.me/submissions/c71e6449-0f3d-47c9-9a57-e729b675f01e

import Definitions.Def_DeletionCode_TraceEditData
import Definitions.Def_DeletionCode_TraceSeparation
import Mathlib.Data.List.OfFn
import Definitions.Def_DeletionCode_AnchorRecords
import Theorems.Thm_DeletionCode_AnchorRecords_packetAt_recordRank
import Theorems.Thm_DeletionCode_AnchorRecords_recordIndex_injective

set_option autoImplicit true
open DeletionCode DeletionCode.AnchorRecords
open AlignmentTrace TraceEditData
namespace DeletionCode.AnchorRecords
theorem _root_.solution (trace : Trace) {n r : ℕ}
    (anchors : Fin r → Fin n) (data : Fin r → Bool × Bool)
    (heq : List.ofFn (fun i => ((anchors i).val, data i)) = encode trace) :
    ∃ e : EditColumn trace → Fin r, Function.Injective e ∧
      ∀ c, (anchors (e c)).val = trace.matchedAnchor c.val.val := by
  have hlen : (encode trace).length = r := by rw [← heq, List.length_ofFn]
  let e : EditColumn trace → Fin r := fun c => Fin.cast hlen (recordIndex trace c)
  refine ⟨e, ?_, ?_⟩
  · intro c d hcd
    apply recordIndex_injective trace
    apply Fin.ext
    have hv : (e c).val = (e d).val := congrArg (fun i : Fin r => i.val) hcd
    exact hv
  · intro c
    have hget := packetAt_recordRank trace c
    rw [← heq] at hget
    have hi : recordRank trace c < r := by
      rw [← hlen]
      exact recordRank_lt trace c
    rw [List.getElem?_ofFn, dif_pos hi] at hget
    exact congrArg Prod.fst (Option.some.inj hget)
end DeletionCode.AnchorRecords
