-- Prove2me | solution 1 for BitDFT.RoutedCountedBlockFreshTapes.concrete_emit_run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T08:26:30.568563+00:00
-- url     : https://prove2.me/submissions/af5c7271-44d6-47a8-a5f8-2b4735afc686

import Definitions.Def_BitDFT_ConcreteEmitFrame
import Theorems.Thm_BitDFT_routed_counted_block_fresh_tapes_v2

set_option autoImplicit false
noncomputable section
open IntMul BitDFT BitDFT.MachineSequence BitDFT.RoutedCountedBlockFreshTapes

private theorem castSerializerCfg_step (M : MultitapeTM) (c : (machine M).Cfg) :
    castSerializerCfg M ((machine M).step c) =
      (serializerEmitContinuation M).machine.step (castSerializerCfg M c) := by
  cases c
  rfl

private theorem castSerializerCfg_run (M : MultitapeTM) (c : (machine M).Cfg) (t : ℕ) :
    castSerializerCfg M ((machine M).step^[t] c) =
      (serializerEmitContinuation M).machine.step^[t] (castSerializerCfg M c) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        castSerializerCfg_step, ih]

theorem solution (M : MultitapeTM) (C : Controller (source M))
    (cEnd : C.machine.Cfg)
    (pre out x y : List Bool)
    (hx : val y + 1 ≤ x.length)
    (hProductCells : cEnd.cells ⟨1, by dsimp [source, IntMul.TrackedOutputShift.machine]; omega⟩ =
      (host M).tapeOf ((pre ++ x).map (host M).bitSym))
    (hProductHead : cEnd.head ⟨1, by dsimp [source, IntMul.TrackedOutputShift.machine]; omega⟩ =
      pre.length + 1) :
    ∃ t : ℕ, t ≤ 6*(val y+1)+4*y.length+2 ∧
      (serializerEmitContinuation M).machine.step^[t]
        (MachineSequence.handoff (suffixControllerOnSerializerHost M C)
          (serializerEmitContinuation M) (suffixEmbed M C
            (fun j p => if j.val < (source M).k then (source M).blank else
              (emitFrame M (emitHostBase M cEnd) (parkedCells M cEnd.cells) (parkedHeads M cEnd.head)
                pre out x y).cells j p)
            (fun j => if j.val < (source M).k then 0 else
              (emitFrame M (emitHostBase M cEnd) (parkedCells M cEnd.cells) (parkedHeads M cEnd.head)
                pre out x y).head j) cEnd)) =
      castSerializerCfg M (embed M (emitHostBase M cEnd) (parkedCells M cEnd.cells) (parkedHeads M cEnd.head)
        (AlphabetEmbedding.embed
          (CountedBlockOnMultiplierAlphabet.alphabetMap (source M))
          (CountedBlock.frame pre out x y y.reverse (val y+1) .halt))) := by
  let base := emitHostBase M cEnd
  have hframe0 := concrete_emit_frame M C cEnd pre out x y hProductCells hProductHead
  have hframe : MachineSequence.handoff (suffixControllerOnSerializerHost M C)
      (serializerEmitContinuation M) (suffixEmbed M C
        (fun j p => if j.val < (source M).k then (source M).blank else
          (emitFrame M base (parkedCells M cEnd.cells) (parkedHeads M cEnd.head)
            pre out x y).cells j p)
        (fun j => if j.val < (source M).k then 0 else
          (emitFrame M base (parkedCells M cEnd.cells) (parkedHeads M cEnd.head)
            pre out x y).head j) cEnd) =
      emitFrame M base (parkedCells M cEnd.cells) (parkedHeads M cEnd.head) pre out x y := by
    simpa [base, emitHostBase, emitFrame] using hframe0
  obtain ⟨t, ht, hrun⟩ := BitDFT.routed_counted_block_fresh_tapes_v2
    M base (parkedCells M cEnd.cells) (parkedHeads M cEnd.head) pre out x y hx
  refine ⟨t, ht, ?_⟩
  rw [hframe]
  have hstart : castSerializerCfg M
      (embed M base (parkedCells M cEnd.cells) (parkedHeads M cEnd.head)
        (AlphabetEmbedding.embed
          (CountedBlockOnMultiplierAlphabet.alphabetMap (source M))
          (CountedBlock.frame pre out x y y.reverse 0 .emit))) =
      emitFrame M base (parkedCells M cEnd.cells) (parkedHeads M cEnd.head) pre out x y := by
    rfl
  have hr := congrArg (castSerializerCfg M) hrun
  rw [castSerializerCfg_run M _ t, hstart] at hr
  exact hr

end
