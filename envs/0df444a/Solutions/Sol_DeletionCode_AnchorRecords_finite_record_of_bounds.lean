-- Prove2me | solution 1 for DeletionCode.AnchorRecords.finite_record_of_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:55:16.185356+00:00
-- url     : https://prove2.me/submissions/602471e4-6ce9-4021-8775-7bba149b212c

import Definitions.Def_DeletionCode_TraceEditData
import Definitions.Def_DeletionCode_TraceSeparation
import Mathlib.Data.List.OfFn
import Definitions.Def_DeletionCode_AnchorRecords

set_option autoImplicit true
open DeletionCode DeletionCode.AnchorRecords
open AlignmentTrace TraceEditData
namespace DeletionCode.AnchorRecords
theorem _root_.solution (packets : List Packet) (n r : ℕ)
    (hlen : packets.length = r) (hbound : ∀ p ∈ packets, p.1 < n) :
    ∃ anchors : Fin r → Fin n, ∃ data : Fin r → Bool × Bool,
      List.ofFn (fun i => ((anchors i).val, data i)) = packets := by
  subst r
  let anchors : Fin packets.length → Fin n :=
    fun i => ⟨(packets.get i).1, hbound _ (List.get_mem packets i)⟩
  refine ⟨anchors, fun i => (packets.get i).2, ?_⟩
  change List.ofFn (packets.get) = packets
  exact List.ofFn_get packets
end DeletionCode.AnchorRecords
