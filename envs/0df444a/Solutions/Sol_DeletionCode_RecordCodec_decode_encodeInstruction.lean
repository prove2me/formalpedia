-- Prove2me | solution 1 for DeletionCode.RecordCodec.decode_encodeInstruction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:00:05.156504+00:00
-- url     : https://prove2.me/submissions/1bb52096-63cb-4896-9d58-e2dc4f462233

import Definitions.Def_DeletionCode_ConcreteDecoder
import Definitions.Def_DeletionCode_DescriptionCount
import Mathlib.Tactic.FinCases
import Definitions.Def_DeletionCode_RecordCodec

set_option autoImplicit true
open DeletionCode DeletionCode.RecordCodec
open HeaderRecovery ConcreteDecoder DescriptionCount
namespace DeletionCode.RecordCodec
theorem _root_.solution (L ν : ℕ) (hL : 1 ≤ L) (hν : 1 ≤ ν)
    (instruction : Instruction (Fin ν)) (hbound : InstructionBounded L instruction) :
    decodeInstruction L ν hν (encodeInstruction L ν hL hν instruction hbound) =
      some (some instruction) := by
  cases instruction with
  | start source sourceSide sourceOffset dest destSide destOffset extra =>
    cases sourceSide <;> cases destSide <;> cases extra <;>
      simp [decodeInstruction, encodeInstruction, instructionField, bitFromNat, bitCode,
        nameFromNat, Nat.mod_eq_of_lt source.isLt, Nat.mod_eq_of_lt dest.isLt]
  | fillBase dest window seedOffset =>
    simp [decodeInstruction, encodeInstruction, instructionField, nameFromNat, slotFromNat,
      Nat.mod_eq_of_lt dest.isLt, Nat.mod_eq_of_lt window.isLt]
  | fillSupplier source sourceSide sourceOffset dest window =>
    cases sourceSide <;>
      simp [decodeInstruction, encodeInstruction, instructionField, bitFromNat, bitCode,
        nameFromNat, slotFromNat, Nat.mod_eq_of_lt source.isLt,
        Nat.mod_eq_of_lt dest.isLt, Nat.mod_eq_of_lt window.isLt]
end DeletionCode.RecordCodec
