-- Prove2me | solution 1 for BitDFT.coordinate_readable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T19:09:05.775861+00:00
-- url     : https://prove2.me/submissions/0ad08fa7-3424-4436-965a-acb6cdbd9246

import Definitions.Def_BitDFT_CoordinateReadable
import Theorems.Thm_BitDFT_signed_block_final_slots
import Theorems.Thm_BitDFT_rewind_tape_correct
import Theorems.Thm_BitDFT_machine_sequence_bound
import Mathlib.Tactic
namespace BitDFT.CoordinateReadable
open IntMul MachineSequence
private theorem positive_not_marker (N : MultitapeTM) (w : List Bool) (p : ℕ) (hp : 0 < p) :
    N.tapeOf (w.map N.bitSym) p ≠ N.startSym := by
  have hd := N.syms_distinct
  simp [List.nodup_cons,List.mem_cons,not_or] at hd
  have hb : N.blank ≠ N.startSym := by aesop
  have hz : N.zero ≠ N.startSym := by aesop
  have ho : N.one ≠ N.startSym := by aesop
  cases p with
  | zero => omega
  | succ p =>
    simp only [MultitapeTM.tapeOf,List.getD_eq_getElem?_getD,List.getElem?_map]
    cases h : w[p]? with
    | none => simpa [h] using hb
    | some b => cases b <;> simp [h,MultitapeTM.bitSym,hz,ho]

private theorem correct_handoff (M : MultitapeTM) (base : (preparation M).Cfg) (p : ℕ)
    (hp : base.head (scratch M) = p) :
    handoff (native (preparation M)) (rewind M) base =
      RewindTape.frame (preparation M) (scratch M) base false p := by
  have hh : Function.update base.head (scratch M) p = base.head := by
    rw [← hp]
    exact Function.update_eq_self _ _
  change MultitapeTM.Cfg.mk _ _ _ = MultitapeTM.Cfg.mk _ _ (Function.update _ _ _)
  rw [hh]
  rfl

end BitDFT.CoordinateReadable
open BitDFT.CoordinateReadable BitDFT IntMul MachineSequence

theorem solution (M : MultitapeTM) (c : (VectorReady.machine M).Cfg)
    (rootCells : ℕ → TapeCopy.Sym) (rootHead : ℕ) (sign : Bool) (x y input extra : List Bool) (T : ℕ)
    (hrun : (preparation M).step^[T] ((preparation M).initCfg input extra) =
      FirstCoordinate.final M c rootCells rootHead sign x y) :
    ∃ t : ℕ, t ≤ T+val y+5 ∧
      (machine M).step^[t] ((machine M).initCfg input extra) = final M c rootCells rootHead sign x y ∧
      ((machine M).step^[t] ((machine M).initCfg input extra)).cells (scratch M) =
        (machine M).tapeOf ((sign::x.take (val y+1)).map (machine M).bitSym) ∧
      ((machine M).step^[t] ((machine M).initCfg input extra)).head (scratch M) = 1 := by
  let base := FirstCoordinate.final M c rootCells rootHead sign x y
  obtain ⟨_,_,hc,hh,_⟩ := BitDFT.signed_block_final_slots (VectorReady.machine M) M.k
    (FirstCoordinate.start M c).cells (FirstCoordinate.start M c).head rootCells rootHead [] [] sign x y
  have hcells : base.cells (scratch M) = (preparation M).tapeOf
      ((sign::x.take (val y+1)).map (preparation M).bitSym) := hc
  have hhead : base.head (scratch M) = val y+3 := by simpa only [base,FirstCoordinate.final,rightCfg,scratch,List.length_nil,Nat.zero_add] using hh
  have hz : base.cells (scratch M) 0 = (preparation M).startSym := by rw [hcells]; rfl
  have hn : ∀ p, 0 < p → base.cells (scratch M) p ≠ (preparation M).startSym := by
    intro p hp
    rw [hcells]
    exact positive_not_marker _ _ _ hp
  have hrw := BitDFT.rewind_tape_correct (preparation M) (scratch M) base hz hn (val y+3)
  have hhalt : ((preparation M).step^[T] ((preparation M).initCfg input extra)).state =
      (native (preparation M)).exit := by rw [hrun]; rfl
  obtain ⟨t,ht,he⟩ := BitDFT.machine_sequence_bound (native (preparation M)) (rewind M)
    ((preparation M).initCfg input extra) T (val y+4) hhalt
  change (machine M).step^[t] ((machine M).initCfg input extra) =
    rightCfg (native (preparation M)) (rewind M)
      ((rewind M).machine.step^[val y+4] (handoff (native (preparation M)) (rewind M)
        ((preparation M).step^[T] ((preparation M).initCfg input extra)))) at he
  rw [hrun,correct_handoff M base _ hhead] at he
  change (machine M).step^[t] ((machine M).initCfg input extra) =
    rightCfg (native (preparation M)) (rewind M)
      ((RewindTape.machine (preparation M) (scratch M)).step^[(val y+3)+1]
        (RewindTape.frame (preparation M) (scratch M) base false (val y+3))) at he
  rw [hrw] at he
  refine ⟨t,by omega,he,?_,?_⟩
  · rw [he]; exact hcells
  · rw [he]; simp [rightCfg,RewindTape.frame]
