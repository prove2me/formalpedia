-- Prove2me | solution 1 for BitDFT.header_offsets_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:55:37.464986+00:00
-- url     : https://prove2.me/submissions/5a4457c9-0b9f-4375-a3de-48164df02504

import Definitions.Def_BitDFT_HeaderOffsets
import Mathlib.Data.List.GetD
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic.FinCases
namespace BitDFT.HeaderOffsetProof
open IntMul MachineSequence
theorem stop_step (M : MultitapeTM) (boundary : M.K) (hne : M.qStart ≠ boundary)
    (c : M.Cfg) (h : c.state ≠ boundary) :
    (stopAt M boundary hne).machine.step (stopCfg M boundary hne c) =
      stopCfg M boundary hne (M.step c) := by
  simp [MultitapeTM.step, stopCfg, stopAt, h]

/-- Exact preservation through the first arrival at an internal boundary. -/
theorem stop_run (M : MultitapeTM) (boundary : M.K) (hne : M.qStart ≠ boundary)
    (c : M.Cfg) (t : ℕ) (h : ∀ s < t, (M.step^[s] c).state ≠ boundary) :
    (stopAt M boundary hne).machine.step^[t] (stopCfg M boundary hne c) =
      stopCfg M boundary hne (M.step^[t] c) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', ih (by intro s hs; exact h s (by omega)),
      stop_step M boundary hne _ (h t (by omega)), Function.iterate_succ_apply']

end BitDFT.HeaderOffsetProof
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


/-- Parse a later field directly from its current input position. -/
private theorem suffix_frame (pre v rest : List Bool) :
    let x := pre ++ List.replicate v.length true ++ false :: (v ++ rest)
    machine.step^[2*v.length+2] (frame x .prefix (pre.length+1) 1 [] 0 []) =
      frame x .copy (pre.length+2*v.length+2) 0 [] 0 v ∧
    ∀ j < 2*v.length+2,
      (machine.step^[j] (frame x .prefix (pre.length+1) 1 [] 0 [])).state ≠ State.copy := by
  let x := pre ++ List.replicate v.length true ++ false :: (v ++ rest)
  change machine.step^[2*v.length+2] (frame x .prefix (pre.length+1) 1 [] 0 []) = _ ∧ _
  let initial := frame x .prefix (pre.length+1) 1 [] 0 []
  have hprefix : ∀ j, j ≤ v.length →
      machine.step^[j] initial =
        frame x .prefix (pre.length+j+1) (j+1) [] j [] := by
    intro j
    induction j with
    | zero => intro _; rfl
    | succ j ih =>
      intro hj
      rw [Function.iterate_succ_apply', ih (by omega)]
      convert prefix_step x (pre.length+j+1) j (by
        have hread := tape_read pre (List.replicate v.length true) (false :: (v++rest)) j
          (by simp; omega)
        simpa [x, MultitapeTM.bitSym, Nat.add_assoc] using hread) using 1 <;> congr 1 <;> omega
  have hdelim : machine.step^[v.length+1] initial =
      frame x .value (pre.length+v.length+2) v.length [] v.length [] := by
    rw [Function.iterate_succ_apply', hprefix _ le_rfl]
    convert delimiter_step x (pre.length+v.length+1) v.length (by
      have hread := tape_read (pre ++ List.replicate v.length true) [false] (v++rest) 0 (by simp)
      simpa [x, MultitapeTM.bitSym] using hread) using 1 <;> congr 1 <;> omega
  have hvalue : ∀ j, j ≤ v.length →
      machine.step^[v.length+1+j] initial =
        frame x .value (pre.length+v.length+2+j) (v.length-j) [] (v.length-j) (v.take j) := by
    intro j
    induction j with
    | zero => intro _; simpa using hdelim
    | succ j ih =>
      intro hj
      have hlt : j < v.length := by omega
      rw [show v.length+1+(j+1)=(v.length+1+j)+1 by omega,
        Function.iterate_succ_apply', ih (by omega)]
      have hr : v.length-j = (v.length-(j+1))+1 := by omega
      rw [hr, List.take_succ_eq_append_getElem hlt]
      convert value_step x (v.take j) (pre.length+v.length+2+j) (v.length-(j+1)) v[j] (by
        have hread := tape_read (pre ++ List.replicate v.length true ++ [false]) v rest j hlt
        simpa [x, List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hread) using 1
        <;> congr 1 <;> omega
  constructor
  · rw [show 2*v.length+2=(v.length+1+v.length)+1 by omega,
      Function.iterate_succ_apply', hvalue _ le_rfl]
    simpa [x, List.append_assoc, two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      value_done x v (pre.length+v.length+2+v.length)
  · intro j hj
    change (machine.step^[j] initial).state ≠ State.copy
    by_cases hp : j ≤ v.length
    · rw [hprefix j hp]
      change State.prefix ≠ State.copy
      decide
    · have he := hvalue (j-(v.length+1)) (by omega)
      have hn : v.length+1+(j-(v.length+1)) = j := by omega
      rw [hn] at he
      rw [he]
      change State.value ≠ State.copy
      decide

/-- This exact later-field run is also available through the frozen-boundary adapter. -/
theorem stopped_suffix (pre v rest : List Bool) :
    let x := pre ++ List.replicate v.length true ++ false :: (v ++ rest)
    (MachineSequence.stopAt machine State.copy (by decide)).machine.step^[2*v.length+2]
      (MachineSequence.stopCfg machine State.copy (by decide)
        (frame x .prefix (pre.length+1) 1 [] 0 [])) =
    MachineSequence.stopCfg machine State.copy (by decide)
      (frame x .copy (pre.length+2*v.length+2) 0 [] 0 v) := by
  dsimp only
  have h := suffix_frame pre v rest
  rw [HeaderOffsetProof.stop_run _ _ _ _ _ h.2, h.1]


private theorem start_at (x : List Bool) (offset : ℕ) :
    machine.step (HeaderOffsets.rawPrepared x offset) = frame x .prefix (offset+1) 1 [] 0 [] := by
  let c := HeaderOffsets.rawPrepared x offset
  have ht : transition c.state (fun i => c.cells i (c.head i)) =
      (.prefix,fun i => (c.cells i (c.head i),Move.right)) := by
    apply Prod.ext
    · rfl
    · funext i
      change HeaderReader.protect (c.cells i (c.head i)) (c.cells i (c.head i),Move.right) = (c.cells i (c.head i),Move.right)
      cases c.cells i (c.head i) <;> rfl
  change machine.step c = _
  apply cfg_ext
  · simp only [MultitapeTM.step,ht]; rfl
  · change (fun i => Function.update (c.cells i) (c.head i) ((transition c.state _).2 i).1) = _
    rw [ht]
    funext i
    fin_cases i <;> exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    funext i; fin_cases i <;> rfl

end BitDFT.HeaderReader
open BitDFT BitDFT.HeaderOffsets IntMul

theorem solution (pre v rest : List Bool) :
    let x := pre ++ List.replicate v.length true ++ false :: (v ++ rest)
    HeaderReader.stage.machine.step^[2*v.length+3] (prepared x pre.length) =
      finished x pre.length v := by
  dsimp only
  let x := pre ++ List.replicate v.length true ++ false :: (v ++ rest)
  change (MachineSequence.stopAt HeaderReader.machine HeaderReader.State.copy (by decide)).machine.step^[2*v.length+3]
      (MachineSequence.stopCfg HeaderReader.machine HeaderReader.State.copy (by decide) (rawPrepared x pre.length)) = _
  rw [show 2*v.length+3=(2*v.length+2)+1 by omega,Function.iterate_succ_apply,
    HeaderOffsetProof.stop_step _ _ _ _ (by intro h; cases h),HeaderReader.start_at]
  exact HeaderReader.stopped_suffix pre v rest
