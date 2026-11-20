-- Prove2me | solution 1 for DeletionCode.RecordSerialization.decode_encodeTotal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:01:54.909698+00:00
-- url     : https://prove2.me/submissions/77b60443-b0a2-4f22-a83e-91bf609525d2

import Definitions.Def_DeletionCode_RecordBounds
import Definitions.Def_DeletionCode_RecordPacking
import Definitions.Def_DeletionCode_RecordSerialization
import Theorems.Thm_DeletionCode_RecordCodec_decode_encodeInstruction


set_option autoImplicit true
open DeletionCode DeletionCode.RecordSerialization
open Windows HeaderRecovery ConcreteDecoder DescriptionCount RecordCodec
open RecordPacking GeneratingModel
namespace DeletionCode.RecordSerialization
theorem _root_.solution (L ν : ℕ) (hL : 1 ≤ L) (hν : 1 ≤ ν)
    (instruction : Instruction (Fin ν)) (hb : InstructionBounded L instruction) :
    decodeInstruction L ν hν (encodeTotal L ν hL hν instruction) = some (some instruction) := by
  simp only [encodeTotal, dif_pos hb]
  exact decode_encodeInstruction L ν hL hν instruction hb
end DeletionCode.RecordSerialization
