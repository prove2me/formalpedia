-- Prove2me | solution 1 for BitDFT.signed_block_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T18:47:12.807637+00:00
-- url     : https://prove2.me/submissions/3d74c90a-1a0f-4e8f-b060-00839808a365

import Definitions.Def_BitDFT_SignedBlock
import Theorems.Thm_BitDFT_counted_block_correct
import Theorems.Thm_BitDFT_machine_sequence_bound
import Mathlib.Data.List.GetD
import Mathlib.Tactic.FinCases

namespace BitDFT.SignedBlock
open IntMul

private theorem cfg_ext (c d : signControl.machine.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c; cases d; cases hs; cases hc; cases hh; rfl

private theorem protect_same (a : TapeCopy.Sym) (d : Move)
    (h : a = .start → d ≠ .left) : HeaderReader.protect a (a,d) = (a,d) := by
  by_cases ha : a = .start
  · simp [HeaderReader.protect, ha, h ha]
  · simp [HeaderReader.protect, ha]

private theorem tape_append (w : List TapeCopy.Sym) (a : TapeCopy.Sym) :
    Function.update (storage.tapeOf w) (w.length + 1) a = storage.tapeOf (w ++ [a]) := by
  funext p
  cases p with
  | zero => simp [MultitapeTM.tapeOf]
  | succ p =>
    by_cases hp : p = w.length
    · subst p; simp [MultitapeTM.tapeOf, List.getD_append_right]
    · rw [Function.update_of_ne (by omega : p+1 ≠ w.length+1)]
      simp only [MultitapeTM.tapeOf]
      by_cases hlt : p < w.length
      · rw [List.getD_append _ _ _ _ hlt]
      · have hge : w.length ≤ p := by omega
        rw [List.getD_eq_default _ _ hge, List.getD_append_right _ _ _ _ hge]
        exact (List.getD_eq_default _ _ (by simp; omega)).symm

theorem block_run (c : storage.Cfg) (t : ℕ) :
    blockControl.machine.step^[t] (blockFrame c) = blockFrame (storage.step^[t] c) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply',ih,Function.iterate_succ_apply']
    rfl

theorem sign_step (pre out : List Bool) (sign : Bool) (x y : List Bool) :
    signControl.machine.step (signStart pre out sign x y) = signFinal pre out sign x y := by
  let c := signStart pre out sign x y
  have h0 : c.cells 0 (c.head 0) = storage.bitSym sign := by
    simp [c,signStart,CountedBlock.frame,MultitapeTM.tapeOf]
  have h1 : c.cells 1 (c.head 1) = TapeCopy.Sym.blank := by
    simp [c,signStart,CountedBlock.frame,MultitapeTM.tapeOf]
  have ht : signTransition c.state (fun i => c.cells i (c.head i)) =
      (true,fun i => (if i = 1 then storage.bitSym sign else c.cells i (c.head i),
        if i = 0 ∨ i = 1 then Move.right else Move.stay)) := by
    apply Prod.ext
    · rfl
    · funext i
      change HeaderReader.protect (c.cells i (c.head i)) _ = _
      fin_cases i
      · exact protect_same _ .right (by intro _; decide)
      · simp [h0,h1,HeaderReader.protect]; cases sign <;> simp [MultitapeTM.bitSym]
      · exact protect_same _ .stay (by intro _; decide)
      · exact protect_same _ .stay (by intro _; decide)
  change signControl.machine.step c = _
  apply cfg_ext
  · change (signTransition c.state (fun i => c.cells i (c.head i))).1 = true
    rw [ht]
  · change (fun i => Function.update (c.cells i) (c.head i) ((signTransition c.state (fun i => c.cells i (c.head i))).2 i).1) = _
    rw [ht]
    funext i
    fin_cases i
    · simpa [c,signStart,signFinal,afterSign,blockFrame,CountedBlock.frame,List.append_assoc] using
        Function.update_eq_self (c.head 0) (c.cells 0)
    · simpa [c,signStart,signFinal,afterSign,blockFrame,CountedBlock.frame,List.map_append] using
        tape_append (out.map storage.bitSym) (storage.bitSym sign)
    · exact Function.update_eq_self _ _
    · exact Function.update_eq_self _ _
  · change (fun i => match ((signTransition c.state (fun i => c.cells i (c.head i))).2 i).2 with
      | .left => c.head i-1 | .stay => c.head i | .right => c.head i+1) = _
    rw [ht]
    funext i
    fin_cases i <;> simp [c,signStart,signFinal,afterSign,blockFrame,CountedBlock.frame,Nat.add_assoc]
end BitDFT.SignedBlock
open BitDFT.SignedBlock BitDFT IntMul MachineSequence

theorem solution (pre out : List Bool) (sign : Bool) (x y : List Bool) (hx : val y+1 ≤ x.length) :
    ∃ t : ℕ, t ≤ 6*(val y+1)+4*y.length+4 ∧
      machine.step^[t] (initial pre out sign x y) = final pre out sign x y := by
  obtain ⟨u,hu,hblock⟩ := BitDFT.counted_block_correct (pre++[sign]) (out++[sign]) x y hx
  have hsign : signControl.machine.step^[1] (signStart pre out sign x y) = signFinal pre out sign x y := by
    simpa using sign_step pre out sign x y
  have hh : (signControl.machine.step^[1] (signStart pre out sign x y)).state = signControl.exit := by
    rw [hsign]; rfl
  obtain ⟨t,ht,he⟩ := BitDFT.machine_sequence_bound signControl blockControl (signStart pre out sign x y) 1 u hh
  rw [hsign] at he
  change machine.step^[t] (initial pre out sign x y) =
    rightCfg signControl blockControl (blockControl.machine.step^[u]
      (blockFrame (CountedBlock.frame (pre++[sign]) (out++[sign]) x y y.reverse 0 .emit))) at he
  rw [block_run,hblock] at he
  exact ⟨t,by omega,he⟩
