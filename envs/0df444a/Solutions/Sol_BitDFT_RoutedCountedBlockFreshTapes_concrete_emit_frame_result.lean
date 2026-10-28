-- Prove2me | solution 1 for BitDFT.RoutedCountedBlockFreshTapes.concrete_emit_frame_result
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T08:26:29.662155+00:00
-- url     : https://prove2.me/submissions/6006f1ca-91be-4d1a-9717-4d7d1f3048f1

import Definitions.Def_BitDFT_ConcreteEmitFrame
set_option autoImplicit false
noncomputable section
open IntMul BitDFT BitDFT.MachineSequence BitDFT.RoutedCountedBlockFreshTapes

theorem solution (M : MultitapeTM) (C : Controller (source M))
    (cEnd : C.machine.Cfg) (pre out x y : List Bool)
    (hProductCells : cEnd.cells ⟨1, by dsimp [source, IntMul.TrackedOutputShift.machine]; omega⟩ =
      (host M).tapeOf ((pre ++ x).map (host M).bitSym))
    (hProductHead : cEnd.head ⟨1, by dsimp [source, IntMul.TrackedOutputShift.machine]; omega⟩ =
      pre.length + 1) :
    MachineSequence.handoff (suffixControllerOnSerializerHost M C)
      (serializerEmitContinuation M)
      (suffixEmbed M C
        (fun j p => if j.val < (source M).k then (source M).blank else
          (emitFrame M
            ⟨(host M).qStart,
              (fun i p => if i.val = 0 then cEnd.cells ⟨0, by
                dsimp [source, IntMul.TrackedOutputShift.machine]; omega⟩ p else (host M).blank),
              (fun i => if i.val = 0 then cEnd.head ⟨0, by
                dsimp [source, IntMul.TrackedOutputShift.machine]; omega⟩ else 0)⟩
            (parkedCells M cEnd.cells) (parkedHeads M cEnd.head) pre out x y).cells j p)
        (fun j => if j.val < (source M).k then 0 else
          (emitFrame M
            ⟨(host M).qStart,
              (fun i p => if i.val = 0 then cEnd.cells ⟨0, by
                dsimp [source, IntMul.TrackedOutputShift.machine]; omega⟩ p else (host M).blank),
              (fun i => if i.val = 0 then cEnd.head ⟨0, by
                dsimp [source, IntMul.TrackedOutputShift.machine]; omega⟩ else 0)⟩
            (parkedCells M cEnd.cells) (parkedHeads M cEnd.head) pre out x y).head j)
        cEnd) =
    ⟨CountedStream.State.emit,
        (emitFrame M
          ⟨(host M).qStart,
            (fun i p => if i.val = 0 then cEnd.cells ⟨0, by
              dsimp [source, IntMul.TrackedOutputShift.machine]; omega⟩ p else (host M).blank),
            (fun i => if i.val = 0 then cEnd.head ⟨0, by
              dsimp [source, IntMul.TrackedOutputShift.machine]; omega⟩ else 0)⟩
          (parkedCells M cEnd.cells) (parkedHeads M cEnd.head) pre out x y).cells,
        (emitFrame M
          ⟨(host M).qStart,
            (fun i p => if i.val = 0 then cEnd.cells ⟨0, by
              dsimp [source, IntMul.TrackedOutputShift.machine]; omega⟩ p else (host M).blank),
            (fun i => if i.val = 0 then cEnd.head ⟨0, by
              dsimp [source, IntMul.TrackedOutputShift.machine]; omega⟩ else 0)⟩
          (parkedCells M cEnd.cells) (parkedHeads M cEnd.head) pre out x y).head⟩ := by
  exact concrete_emit_frame M C cEnd pre out x y hProductCells hProductHead

end
