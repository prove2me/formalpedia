-- Prove2me | solution 1 for DeletionCode.RecordSerialization.description_roundtrip
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:02:52.414761+00:00
-- url     : https://prove2.me/submissions/2038d7e3-edbf-4bea-a6ed-46ec08d92737

import Definitions.Def_DeletionCode_RecordBounds
import Definitions.Def_DeletionCode_RecordPacking
import Definitions.Def_DeletionCode_RecordSerialization
import Theorems.Thm_DeletionCode_RecordSerialization_decode_encodeTotal
import Theorems.Thm_DeletionCode_RecordSerialization_roots_roundtrip
import Theorems.Thm_DeletionCode_RecordCodec_decode_encodeHeader
import Theorems.Thm_DeletionCode_RecordCodec_decode_zeroRow
import Theorems.Thm_DeletionCode_RecordPacking_unpack_pack


set_option autoImplicit true
open DeletionCode DeletionCode.RecordSerialization
open Windows HeaderRecovery ConcreteDecoder DescriptionCount RecordCodec
open RecordPacking GeneratingModel
namespace DeletionCode.RecordSerialization
theorem _root_.solution (x : Letters) (n k ν c : ℕ) (hν : 1 ≤ ν)
    (header : Fin ν → Header)
    (hlo : ∀ b, 1 ≤ (header b).rho) (hhi : ∀ b, (header b).rho ≤ windowLength k)
    (roots : List (Fin ν × ℕ)) (hroots : roots.length = c)
    (hpos : ∀ b a, (b, a) ∈ roots → a < n)
    (instructions : List (Instruction (Fin ν))) (hcost : instructions.length ≤ 4 * ν)
    (hbounded : ∀ instruction ∈ instructions, InstructionBounded (windowLength k) instruction) :
    decodeDescription x n k ν c hν
      (encodeDescription n k ν c hν header hlo hhi roots hroots hpos instructions) =
      (decode x n k header roots instructions).map (dataOfOutput k header) := by
  let hL : 1 ≤ windowLength k := by unfold windowLength; omega
  have hheader : (fun b => decodeHeader (encodeHeader (windowLength k) (header b) (hlo b) (hhi b))) =
      header := by
    funext b
    exact decode_encodeHeader (windowLength k) (header b) (hlo b) (hhi b)
  have hinstructions := unpack_pack (decodeInstruction (windowLength k) ν hν)
    (encodeTotal (windowLength k) ν hL hν) (zeroRow (windowLength k) ν hL hν)
    (decode_zeroRow (windowLength k) ν hL hν) instructions
    (fun a ha => decode_encodeTotal (windowLength k) ν hL hν a (hbounded a ha))
    (4 * ν) hcost
  unfold decodeDescription encodeDescription
  dsimp only
  rw [hheader, roots_roundtrip n ν c roots hroots hpos, hinstructions]
  rfl
end DeletionCode.RecordSerialization
