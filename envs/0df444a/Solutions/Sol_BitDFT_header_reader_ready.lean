-- Prove2me | solution 1 for BitDFT.header_reader_ready
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T14:00:34.299364+00:00
-- url     : https://prove2.me/submissions/99c6b640-6e38-47c4-a57f-51fad6ef24ed

import Definitions.Def_BitDFT_HeaderReader
import Mathlib.Data.List.GetD
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic.FinCases

namespace BitDFT.HeaderReader
open IntMul

private theorem cfg_ext (c d : machine.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c; cases d; cases hs; cases hc; cases hh; rfl

private theorem tape_append (w : List Sym) (a : Sym) :
    Function.update (machine.tapeOf w) (w.length + 1) a = machine.tapeOf (w ++ [a]) := by
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

private theorem tape_erase (w : List Sym) (a : Sym) :
    Function.update (machine.tapeOf (w ++ [a])) (w.length + 1) .blank = machine.tapeOf w := by
  rw [← tape_append]
  rw [Function.update_idem]
  have he : machine.tapeOf w (w.length+1) = TapeCopy.Sym.blank := by
    simp [MultitapeTM.tapeOf]
  rw [← he]
  exact Function.update_eq_self _ _

private def frame (x : List Bool) (q : State) (ip cp : ℕ)
    (out : List Bool) (count : ℕ) (v : List Bool) : machine.Cfg where
  state := q
  cells := fun i => if i = 0 then machine.tapeOf (x.map machine.bitSym ++ [TapeCopy.Sym.sep])
    else if i = 1 then machine.tapeOf (out.map machine.bitSym)
    else if i = 2 then machine.tapeOf (List.replicate count TapeCopy.Sym.one)
    else machine.tapeOf (v.map machine.bitSym)
  head := fun i => if i = 0 then ip else if i = 1 then out.length+1
    else if i = 2 then cp else v.length+1

private lemma reads_out (x out v : List Bool) (q : State) (ip cp c : ℕ) :
    (frame x q ip cp out c v).cells 1 ((frame x q ip cp out c v).head 1) = TapeCopy.Sym.blank := by
  simp [frame, MultitapeTM.tapeOf]

private lemma reads_val (x out v : List Bool) (q : State) (ip cp c : ℕ) :
    (frame x q ip cp out c v).cells 3 ((frame x q ip cp out c v).head 3) = TapeCopy.Sym.blank := by
  simp [frame, MultitapeTM.tapeOf]

private lemma prefix_step (x : List Bool) (ip j : ℕ)
    (hi : machine.tapeOf (x.map machine.bitSym ++ [TapeCopy.Sym.sep]) ip = TapeCopy.Sym.one) :
    machine.step (frame x .prefix ip (j+1) [] j []) =
      frame x .prefix (ip+1) (j+2) [] (j+1) [] := by
  let c := frame x .prefix ip (j+1) [] j []
  have h0 : c.cells 0 (c.head 0) = TapeCopy.Sym.one := hi
  have h1 : c.cells 1 (c.head 1) = TapeCopy.Sym.blank := reads_out ..
  have h2 : c.cells 2 (c.head 2) = TapeCopy.Sym.blank := by simp [c, frame, MultitapeTM.tapeOf]
  have h3 : c.cells 3 (c.head 3) = TapeCopy.Sym.blank := reads_val ..
  have ht : transition c.state (fun i => c.cells i (c.head i)) =
      (.prefix, fun i => if i = 0 ∨ i = 2 then (TapeCopy.Sym.one, Move.right) else (TapeCopy.Sym.blank, Move.stay)) := by
    change transition State.prefix _ = _
    apply Prod.ext
    · simp [transition, raw, h0]
    · funext i; fin_cases i <;> simp [transition, raw, h0, h1, h2, h3, protect]
  change machine.step c = _
  apply cfg_ext
  · simp only [MultitapeTM.step, ht]; rfl
  · change (fun i => Function.update (c.cells i) (c.head i)
      ((transition c.state (fun i => c.cells i (c.head i))).2 i).1) = _
    rw [ht]
    funext i
    fin_cases i
    · change Function.update (c.cells 0) ip TapeCopy.Sym.one = c.cells 0
      rw [← hi]; exact Function.update_eq_self _ _
    · change Function.update (c.cells 1) 1 TapeCopy.Sym.blank = c.cells 1
      rw [← h1]; exact Function.update_eq_self _ _
    · change Function.update (machine.tapeOf (List.replicate j TapeCopy.Sym.one)) (j+1) TapeCopy.Sym.one =
        machine.tapeOf (List.replicate (j+1) TapeCopy.Sym.one)
      have hp := tape_append (List.replicate j TapeCopy.Sym.one) TapeCopy.Sym.one
      simpa [List.replicate_add] using hp
    · change Function.update (c.cells 3) 1 TapeCopy.Sym.blank = c.cells 3
      rw [← h3]; exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step, ht]
    funext i; fin_cases i <;> simp [c, frame]


private lemma protect_stay (a : Sym) : protect a (a, .stay) = (a, .stay) := by
  cases a <;> rfl

private lemma same_cells (c : machine.Cfg) (q : State) (d : Fin 4 → Move)
    (ht : transition c.state (fun i => c.cells i (c.head i)) =
      (q, fun i => (c.cells i (c.head i), d i))) :
    (machine.step c).cells = c.cells := by
  simp only [MultitapeTM.step, ht]
  funext i
  exact Function.update_eq_self _ _

private lemma start_step (x : List Bool) :
    machine.step (machine.initCfg x []) = frame x .prefix 1 1 [] 0 [] := by
  apply cfg_ext
  · rfl
  · funext i
    fin_cases i <;> exact Function.update_eq_self 0 _
  · funext i; fin_cases i <;> rfl

private lemma delimiter_step (x : List Bool) (ip j : ℕ)
    (hi : machine.tapeOf (x.map machine.bitSym ++ [TapeCopy.Sym.sep]) ip = TapeCopy.Sym.zero) :
    machine.step (frame x .prefix ip (j+1) [] j []) =
      frame x .value (ip+1) j [] j [] := by
  let c := frame x .prefix ip (j+1) [] j []
  have h0 : c.cells 0 (c.head 0) = TapeCopy.Sym.zero := hi
  have h1 : c.cells 1 (c.head 1) = TapeCopy.Sym.blank := reads_out ..
  have h2 : c.cells 2 (c.head 2) = TapeCopy.Sym.blank := by simp [c, frame, MultitapeTM.tapeOf]
  have h3 : c.cells 3 (c.head 3) = TapeCopy.Sym.blank := reads_val ..
  have ht : transition c.state (fun i => c.cells i (c.head i)) =
      (.value, fun i => (c.cells i (c.head i),
        if i = 0 then Move.right else if i = 2 then Move.left else Move.stay)) := by
    change transition State.prefix _ = _
    apply Prod.ext
    · simp [transition, raw, h0]
    · funext i; fin_cases i <;> simp [transition, raw, h0, h1, h2, h3, protect]
  change machine.step c = _
  apply cfg_ext
  · simp only [MultitapeTM.step, ht]; rfl
  · exact same_cells c _ _ ht
  · simp only [MultitapeTM.step, ht]
    funext i; fin_cases i <;> simp [c, frame]

private lemma value_step (x v : List Bool) (ip j : ℕ) (b : Bool)
    (hi : machine.tapeOf (x.map machine.bitSym ++ [TapeCopy.Sym.sep]) ip = machine.bitSym b) :
    machine.step (frame x .value ip (j+1) [] (j+1) v) =
      frame x .value (ip+1) j [] j (v ++ [b]) := by
  let c := frame x .value ip (j+1) [] (j+1) v
  have h0 : c.cells 0 (c.head 0) = machine.bitSym b := hi
  have h1 : c.cells 1 (c.head 1) = TapeCopy.Sym.blank := reads_out ..
  have h2 : c.cells 2 (c.head 2) = TapeCopy.Sym.one := by
    simp [c, frame, MultitapeTM.tapeOf]
  have h3 : c.cells 3 (c.head 3) = TapeCopy.Sym.blank := reads_val ..
  have ht : transition c.state (fun i => c.cells i (c.head i)) =
      (.value, fun i => if i = 0 then (machine.bitSym b, Move.right)
        else if i = 1 then (TapeCopy.Sym.blank, Move.stay)
        else if i = 2 then (TapeCopy.Sym.blank, Move.left) else (machine.bitSym b, Move.right)) := by
    change transition State.value _ = _
    apply Prod.ext
    · simp [transition, raw, h2]
    · funext i; fin_cases i <;> cases b <;>
        simp [transition, raw, h0, h1, h2, h3, protect, MultitapeTM.bitSym]
  change machine.step c = _
  apply cfg_ext
  · simp only [MultitapeTM.step, ht]; rfl
  · change (fun i => Function.update (c.cells i) (c.head i)
      ((transition c.state (fun i => c.cells i (c.head i))).2 i).1) = _
    rw [ht]
    funext i; fin_cases i
    · change Function.update (c.cells 0) ip (machine.bitSym b) = c.cells 0
      rw [← h0]; exact Function.update_eq_self _ _
    · change Function.update (c.cells 1) 1 TapeCopy.Sym.blank = c.cells 1
      rw [← h1]; exact Function.update_eq_self _ _
    · change Function.update (machine.tapeOf (List.replicate (j+1) TapeCopy.Sym.one)) (j+1) TapeCopy.Sym.blank =
        machine.tapeOf (List.replicate j TapeCopy.Sym.one)
      simpa [List.replicate_add] using tape_erase (List.replicate j TapeCopy.Sym.one) TapeCopy.Sym.one
    · change Function.update (machine.tapeOf (v.map machine.bitSym)) (v.length+1)
        (machine.bitSym b) = machine.tapeOf ((v ++ [b]).map machine.bitSym)
      simpa using tape_append (v.map machine.bitSym) (machine.bitSym b)
  · simp only [MultitapeTM.step, ht]
    funext i; fin_cases i <;> simp [c, frame]

private lemma value_done (x v : List Bool) (ip : ℕ) :
    machine.step (frame x .value ip 0 [] 0 v) = frame x .copy ip 0 [] 0 v := by
  let c := frame x .value ip 0 [] 0 v
  have h2 : c.cells 2 (c.head 2) = TapeCopy.Sym.start := rfl
  have ht : transition c.state (fun i => c.cells i (c.head i)) =
      (.copy, fun i => (c.cells i (c.head i), Move.stay)) := by
    change transition State.value _ = _
    simp [transition, raw, h2, protect_stay]
  change machine.step c = _
  apply cfg_ext
  · simp only [MultitapeTM.step, ht]; rfl
  · exact same_cells c _ _ ht
  · simp only [MultitapeTM.step, ht]; rfl

private lemma copy_step (x out v : List Bool) (ip : ℕ) (b : Bool)
    (hi : machine.tapeOf (x.map machine.bitSym ++ [TapeCopy.Sym.sep]) ip = machine.bitSym b) :
    machine.step (frame x .copy ip 0 out 0 v) = frame x .copy (ip+1) 0 (out++[b]) 0 v := by
  let c := frame x .copy ip 0 out 0 v
  have h0 : c.cells 0 (c.head 0) = machine.bitSym b := hi
  have h1 : c.cells 1 (c.head 1) = TapeCopy.Sym.blank := reads_out ..
  have h2 : c.cells 2 (c.head 2) = TapeCopy.Sym.start := rfl
  have h3 : c.cells 3 (c.head 3) = TapeCopy.Sym.blank := reads_val ..
  have ht : transition c.state (fun i => c.cells i (c.head i)) =
      (.copy, fun i => if i = 0 ∨ i = 1 then (machine.bitSym b, Move.right)
        else (c.cells i (c.head i), Move.stay)) := by
    change transition State.copy _ = _
    apply Prod.ext
    · cases b <;> simp [transition, raw, h0, MultitapeTM.bitSym]
    · funext i; fin_cases i <;> cases b <;>
        simp [transition, raw, h0, h1, h2, h3, protect, MultitapeTM.bitSym]
  change machine.step c = _
  apply cfg_ext
  · simp only [MultitapeTM.step, ht]; rfl
  · change (fun i => Function.update (c.cells i) (c.head i)
      ((transition c.state (fun i => c.cells i (c.head i))).2 i).1) = _
    rw [ht]
    funext i; fin_cases i
    · change Function.update (c.cells 0) ip (machine.bitSym b) = c.cells 0
      rw [← h0]; exact Function.update_eq_self _ _
    · change Function.update (machine.tapeOf (out.map machine.bitSym)) (out.length+1)
        (machine.bitSym b) = machine.tapeOf ((out++[b]).map machine.bitSym)
      simpa using tape_append (out.map machine.bitSym) (machine.bitSym b)
    · exact Function.update_eq_self _ _
    · exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step, ht]
    funext i; fin_cases i <;> simp [c, frame]

private lemma copy_done (x out v : List Bool) (ip : ℕ)
    (hi : machine.tapeOf (x.map machine.bitSym ++ [TapeCopy.Sym.sep]) ip = TapeCopy.Sym.sep) :
    machine.step (frame x .copy ip 0 out 0 v) = frame x .halt ip 0 out 0 v := by
  let c := frame x .copy ip 0 out 0 v
  have h0 : c.cells 0 (c.head 0) = TapeCopy.Sym.sep := hi
  have ht : transition c.state (fun i => c.cells i (c.head i)) =
      (.halt, fun i => (c.cells i (c.head i), Move.stay)) := by
    change transition State.copy _ = _
    simp [transition, raw, h0, protect_stay]
  change machine.step c = _
  apply cfg_ext
  · simp only [MultitapeTM.step, ht]; rfl
  · exact same_cells c _ _ ht
  · simp only [MultitapeTM.step, ht]; rfl


private lemma tape_read (pre w post : List Bool) (j : ℕ) (hj : j < w.length) :
    machine.tapeOf ((pre ++ w ++ post).map machine.bitSym ++ [TapeCopy.Sym.sep])
      (pre.length + j + 1) = machine.bitSym w[j] := by
  simp only [MultitapeTM.tapeOf, List.map_append, List.append_assoc]
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp only [List.length_map, Nat.add_sub_cancel_left]
  rw [List.getD_append _ _ _ _ (by simpa using hj)]
  rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map]

private lemma tape_sep (x : List Bool) :
    machine.tapeOf (x.map machine.bitSym ++ [TapeCopy.Sym.sep]) (x.length+1) =
      TapeCopy.Sym.sep := by
  simp [MultitapeTM.tapeOf]

private theorem ready_frame (v rest : List Bool) :
    machine.step^[2 * v.length + 3]
      (machine.initCfg (List.replicate v.length true ++ false :: (v ++ rest)) []) =
    frame (List.replicate v.length true ++ false :: (v ++ rest)) .copy
      (2 * v.length + 2) 0 [] 0 v := by
  let x := List.replicate v.length true ++ false :: (v ++ rest)
  have hprefix : ∀ j, j ≤ v.length →
      machine.step^[j+1] (machine.initCfg x []) = frame x .prefix (j+1) (j+1) [] j [] := by
    intro j
    induction j with
    | zero => intro _; simpa using start_step x
    | succ j ih =>
      intro hj
      rw [Function.iterate_succ_apply', ih (by omega)]
      apply prefix_step
      have hread := tape_read [] (List.replicate v.length true) (false :: (v++rest)) j
        (by simp; omega)
      simpa [x, MultitapeTM.bitSym] using hread
  have hdelim : machine.step^[v.length+2] (machine.initCfg x []) =
      frame x .value (v.length+2) v.length [] v.length [] := by
    rw [show v.length+2=(v.length+1)+1 by omega, Function.iterate_succ_apply', hprefix _ le_rfl]
    apply delimiter_step
    have hread := tape_read (List.replicate v.length true) [false] (v++rest) 0 (by simp)
    simpa [x, MultitapeTM.bitSym] using hread
  have hvalue : ∀ j, j ≤ v.length →
      machine.step^[v.length+2+j] (machine.initCfg x []) =
        frame x .value (v.length+2+j) (v.length-j) [] (v.length-j) (v.take j) := by
    intro j
    induction j with
    | zero => intro _; simpa using hdelim
    | succ j ih =>
      intro hj
      have hlt : j < v.length := by omega
      rw [show v.length+2+(j+1)=(v.length+2+j)+1 by omega,
        Function.iterate_succ_apply', ih (by omega)]
      have hr : v.length-j = (v.length-(j+1))+1 := by omega
      rw [hr, List.take_succ_eq_append_getElem hlt]
      apply value_step
      have hread := tape_read (List.replicate v.length true ++ [false]) v rest j hlt
      simpa [x, List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hread
  have hcopy0 : machine.step^[2*v.length+3] (machine.initCfg x []) =
      frame x .copy (2*v.length+2) 0 [] 0 v := by
    rw [show 2*v.length+3=(v.length+2+v.length)+1 by omega,
      Function.iterate_succ_apply', hvalue _ le_rfl]
    simpa [two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      value_done x v (v.length+2+v.length)
  exact hcopy0

end BitDFT.HeaderReader

open BitDFT.HeaderReader

theorem solution (v rest : List Bool) :
    let x := List.replicate v.length true ++ false :: (v ++ rest)
    let c := machine.step^[2 * v.length + 3] (machine.initCfg x [])
    c.state = State.copy ∧ c.head 0 = 2 * v.length + 2 ∧
      c.cells 3 = machine.tapeOf (v.map machine.bitSym) ∧
      c.cells 2 = machine.tapeOf [] ∧ c.head 2 = 0 ∧
      c.cells 1 = machine.tapeOf [] ∧ c.head 1 = 1 ∧ c.head 3 = v.length+1 := by
  dsimp only
  rw [ready_frame]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
