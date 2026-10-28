-- Prove2me | solution 1 for BitDFT.tracked_call_emit_serializer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T08:39:06.958244+00:00
-- url     : https://prove2.me/submissions/52b1205c-deab-425b-8dd0-e19acab87345

import Definitions.Def_IntMul_TrackedBankedCall
import Definitions.Def_IntMul_TrackedOutputShift
import Definitions.Def_BitDFT_BitAdvance
import Definitions.Def_BitDFT_RewindTape
import Definitions.Def_BitDFT_MachineSequence
import Definitions.Def_BitDFT_LiftController
import Definitions.Def_BitDFT_ConcreteEmitFrame
import Theorems.Thm_BitDFT_tracked_call_product_suffix
import Theorems.Thm_BitDFT_routed_counted_block_fresh_tapes_v2
import Mathlib.Tactic

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

theorem concrete_emit_run_local (M : MultitapeTM) (C : Controller (source M))
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


private theorem taggedGetD (M : MultitapeTM) (w : List M.Sym) (i : ℕ) :
    (w.map (fun a => some (a,true))).getD i (some (M.blank,false)) =
      some (w.getD i M.blank, decide (i < w.length)) := by
  by_cases hi : i < w.length
  · rw [List.getD_eq_getElem _ _ (by simpa using hi),
      List.getD_eq_getElem _ _ hi]
    simp [hi]
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hi),
      List.getD_eq_default _ _ (Nat.le_of_not_gt hi)]
    simp [hi]

private theorem shiftedOutputTape (M : MultitapeTM)
    (base : ℕ → TrackedBankedSimulation.Sym M) (w : List Bool)
    (hm : base 0 = (TrackedOutputShift.machine M).startSym) :
    TrackedOutputShift.outputTape M base w =
      (TrackedOutputShift.machine M).tapeOf
        (w.map (TrackedOutputShift.machine M).bitSym) := by
  funext p
  cases p with
  | zero => exact hm
  | succ p =>
      have ht := taggedGetD M (w.map M.bitSym) p
      have he : (w.map M.bitSym).map (fun a => some (a,true)) =
          w.map (TrackedOutputShift.machine M).bitSym := by
        rw [List.map_map]
        congr 1
        funext b
        cases b <;> rfl
      have hl : (w.map M.bitSym).length = w.length := by simp
      rw [hl, he] at ht
      exact ht.symm

theorem solution (M : MultitapeTM)
    (base : (TrackedBankedCall.machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (productWord : List Bool)
    (counter : Fin (TrackedOutputShift.machine M).k)
    (hcounterProduct : counter ≠ ⟨1, by dsimp [TrackedOutputShift.machine]; omega⟩)
    (counterHead p L : ℕ) (hp : p = productWord.length + 1)
    (hcounterHead :
      (TrackedBankedCall.finalFrame M base 1 offset extent c productWord).head counter = counterHead)
    (hmarker :
      (TrackedBankedCall.finalFrame M base 1 offset extent c productWord).cells
        ⟨1, by dsimp [TrackedOutputShift.machine]; omega⟩ 0 =
          (TrackedOutputShift.machine M).startSym)
    (hbits : ∀ r, r < L →
      (TrackedBankedCall.finalFrame M base 1 offset extent c productWord).cells counter
        (counterHead+r) = (TrackedOutputShift.machine M).zero ∨
      (TrackedBankedCall.finalFrame M base 1 offset extent c productWord).cells counter
        (counterHead+r) = (TrackedOutputShift.machine M).one)
    (hstop :
      (TrackedBankedCall.finalFrame M base 1 offset extent c productWord).cells counter
        (counterHead+L) ≠ (TrackedOutputShift.machine M).zero ∧
      (TrackedBankedCall.finalFrame M base 1 offset extent c productWord).cells counter
        (counterHead+L) ≠ (TrackedOutputShift.machine M).one)
    (hL : L ≤ productWord.length) (out y : List Bool)
    (hfit : val y + 1 ≤ (productWord.drop L).length) :
    let product : Fin (TrackedOutputShift.machine M).k :=
      ⟨1, by dsimp [TrackedOutputShift.machine]; omega⟩
    let callFrame := TrackedBankedCall.finalFrame M base 1 offset extent c productWord
    let shiftStart : (TrackedOutputShift.machine M).Cfg :=
      ⟨.rewind, callFrame.cells, callFrame.head⟩
    let shifted := TrackedOutputShift.finalFrame M shiftStart productWord
    let P := MachineSequence.native (TrackedOutputShift.machine M)
    let Q := RewindTape.control P.machine product
    let R := BitAdvance.control P.machine product counter (Ne.symm hcounterProduct)
    let V := MachineSequence.sequence Q R
    let Vflat := MachineSequence.liftController P V
    let C := MachineSequence.sequence P Vflat
    let cEnd := MachineSequence.rightCfg P Vflat
      (MachineSequence.rightCfg Q R
        (BitAdvance.frame P.machine product counter (Ne.symm hcounterProduct)
          shifted true (L+1) (counterHead+L)))
    ∃ ts tr : ℕ,
      ts ≤ 4*productWord.length+4+(p+L+3)+1 ∧
      tr ≤ 6*(val y+1)+4*y.length+2 ∧
      C.machine.step^[ts] (MachineSequence.leftCfg P Vflat shiftStart) = cEnd ∧
      (serializerEmitContinuation M).machine.step^[tr]
        (MachineSequence.handoff (suffixControllerOnSerializerHost M C)
          (serializerEmitContinuation M) (suffixEmbed M C
            (fun j q => if j.val < (source M).k then (source M).blank else
              (emitFrame M (emitHostBase M cEnd) (parkedCells M cEnd.cells)
                (parkedHeads M cEnd.head) (productWord.take L) out
                (productWord.drop L) y).cells j q)
            (fun j => if j.val < (source M).k then 0 else
              (emitFrame M (emitHostBase M cEnd) (parkedCells M cEnd.cells)
                (parkedHeads M cEnd.head) (productWord.take L) out
                (productWord.drop L) y).head j) cEnd)) =
      castSerializerCfg M (embed M (emitHostBase M cEnd)
        (parkedCells M cEnd.cells) (parkedHeads M cEnd.head)
        (AlphabetEmbedding.embed
          (CountedBlockOnMultiplierAlphabet.alphabetMap (source M))
          (CountedBlock.frame (productWord.take L) out (productWord.drop L) y
            y.reverse (val y+1) .halt))) := by
  let product : Fin (TrackedOutputShift.machine M).k :=
    ⟨1, by dsimp [TrackedOutputShift.machine]; omega⟩
  let callFrame := TrackedBankedCall.finalFrame M base 1 offset extent c productWord
  let shiftStart : (TrackedOutputShift.machine M).Cfg :=
    ⟨.rewind, callFrame.cells, callFrame.head⟩
  let shifted := TrackedOutputShift.finalFrame M shiftStart productWord
  let P := MachineSequence.native (TrackedOutputShift.machine M)
  let Q := RewindTape.control P.machine product
  let R := BitAdvance.control P.machine product counter (Ne.symm hcounterProduct)
  let V := MachineSequence.sequence Q R
  let Vflat := MachineSequence.liftController P V
  let C := MachineSequence.sequence P Vflat
  let cEnd := MachineSequence.rightCfg P Vflat
    (MachineSequence.rightCfg Q R
      (BitAdvance.frame P.machine product counter (Ne.symm hcounterProduct)
        shifted true (L+1) (counterHead+L)))
  obtain ⟨ts, hts, hrun⟩ := BitDFT.tracked_call_product_suffix
    M base offset extent c productWord counter hcounterProduct counterHead p L hp
    hcounterHead hmarker hbits hstop
  have hrun' : C.machine.step^[ts] (MachineSequence.leftCfg P Vflat shiftStart) = cEnd := by
    simpa [product, callFrame, shiftStart, shifted, P, Q, R, V, Vflat, C, cEnd] using hrun
  have hsource : shifted.cells product =
      (source M).tapeOf (productWord.map (source M).bitSym) := by
    have hm : callFrame.cells product 0 = (source M).startSym := by
      simpa [callFrame, product] using hmarker
    have ht := shiftedOutputTape M (callFrame.cells product) productWord hm
    simpa [shifted, TrackedOutputShift.finalFrame, product] using ht
  have hcells : cEnd.cells product =
      (source M).tapeOf (productWord.map (source M).bitSym) := by
    simpa [cEnd, MachineSequence.rightCfg, BitAdvance.frame, shifted, product] using hsource
  have hproductCells :
      cEnd.cells ⟨1, by dsimp [source, TrackedOutputShift.machine]; omega⟩ =
        (host M).tapeOf (((productWord.take L) ++ (productWord.drop L)).map (host M).bitSym) := by
    have hsplit : productWord.take L ++ productWord.drop L = productWord :=
      List.take_append_drop L productWord
    have hidx : (⟨1, by dsimp [source, TrackedOutputShift.machine]; omega⟩ :
        Fin (source M).k) = product := by
      apply Fin.ext
      rfl
    rw [hidx, hcells, hsplit]
    rfl
  have hhead : cEnd.head ⟨1, by dsimp [source, TrackedOutputShift.machine]; omega⟩ =
      (productWord.take L).length + 1 := by
    have hlen : (productWord.take L).length = L := by
      simp [List.length_take, Nat.min_eq_left hL]
    have hcp : counter ≠ product := by
      simpa [product] using hcounterProduct
    have hidx2 : (⟨1, by dsimp [source, TrackedOutputShift.machine]; omega⟩ :
        Fin (source M).k) = product := by
      apply Fin.ext
      rfl
    have hsourceHead : cEnd.head product = L+1 := by
      change Function.update (Function.update shifted.head product (L+1))
        counter (counterHead+L) product = L+1
      rw [Function.update_of_ne (Ne.symm hcp)]
      simp
    simpa [hidx2, hlen] using hsourceHead
  obtain ⟨tr, htr, hser⟩ := concrete_emit_run_local M C cEnd
    (productWord.take L) out (productWord.drop L) y hfit hproductCells hhead
  exact ⟨ts, tr, hts, htr, hrun', hser⟩

end
