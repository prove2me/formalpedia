-- Prove2me | solution 1 for BitDFT.retained_precision
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T18:02:49.113989+00:00
-- url     : https://prove2.me/submissions/d0c2feab-8c8b-4bb0-a434-7f1a8972fcfd

import Definitions.Def_BitDFT_RewriteInput
import Mathlib.Tactic
open BitDFT IntMul

/-- The input rewriter leaves canonical precision and dimension on its work tapes. -/
theorem solution (n b : ℕ) (rest v : List Bool)
    (hv : BinaryCounter.value v = guardPrecision n b) :
    (RewriteInput.final n b rest v).cells 3 = RewriteInput.machine.tapeOf
      ((bin (guardPrecision n b).size (guardPrecision n b)).map RewriteInput.machine.bitSym) ∧
    (RewriteInput.final n b rest v).head 3 = (guardPrecision n b).size+1 ∧
    (RewriteInput.final n b rest v).cells 4 = RewriteInput.machine.tapeOf
      ((true :: (bin n.size n).tail).map RewriteInput.machine.bitSym) ∧
    (RewriteInput.final n b rest v).head 4 = (true :: (bin n.size n).tail).length+1 := by
  simp [RewriteInput.final,RewriteInput.copyBase,SuffixCopy.frame,RewriteHeaders.final,
    HeaderSerialization.final,HeaderSerialization.precisionFinished,
    HeaderSerialization.serializerBase,HeaderSerialization.trimmed,
    HeaderSerialization.trimBase,HeaderSerialization.firstFinished,
    HeaderSerialization.inputBase,SerializeField.frame,TrimReverse.frame,
    TapePermutation.embed,HeaderSerialization.swap34,MachineSequence.rightCfg,hv,
    bin]
  exact ⟨rfl,rfl⟩
