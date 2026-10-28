-- Prove2me | solution 1 for BitDFT.BankedOperandStageProof.coordinate_pair_to_halt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T15:30:06.14381+00:00
-- url     : https://prove2.me/submissions/faab7e40-970b-4a06-a147-b2a80cf426eb

import Definitions.Def_BitDFT_OperandStage
import Definitions.Def_BitDFT_BankedOperandStageProofSupport
import Mathlib.Data.List.GetD
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
namespace BitDFT.BankedOperandStageProof
open IntMul BitDFT.OperandStage BitDFT.MachineSequence BitDFT.BankedOperandStageProofSupport

private theorem cfg_ext {N : MultitapeTM} (P : Controller N)
    (c d : P.machine.Cfg) (hs : c.state = d.state)
    (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem protect_self_move {N : MultitapeTM} (a : N.Sym) (m : Move)
    (hm : m ≠ Move.left) : protect a a m = (a, m) := by
  by_cases h : a = N.startSym <;> simp [protect, h, hm]

private theorem tape_append (N : MultitapeTM) (w : List N.Sym) (a : N.Sym) :
    Function.update (N.tapeOf w) (w.length + 1) a = N.tapeOf (w ++ [a]) := by
  funext p
  cases p with
  | zero => simp [MultitapeTM.tapeOf]
  | succ p =>
    by_cases hp : p = w.length
    · subst p
      simp [MultitapeTM.tapeOf, List.getD_append_right]
    · rw [Function.update_of_ne (by omega : p + 1 ≠ w.length + 1)]
      simp only [MultitapeTM.tapeOf]
      by_cases hlt : p < w.length
      · rw [List.getD_append _ _ _ _ hlt]
      · have hge : w.length ≤ p := by omega
        rw [List.getD_eq_default _ _ hge, List.getD_append_right _ _ _ _ hge]
        exact (List.getD_eq_default _ _ (by simp; omega)).symm

private def fillFrame {N : MultitapeTM} (coord dim out : Fin N.k)
    (hc : coord ≠ N.inTape) (hd : dim ≠ N.inTape) (ho : out ≠ N.inTape)
    (hcd : coord ≠ dim) (hco : coord ≠ out) (hdo : dim ≠ out)
    (c : (control N coord dim out hc hd ho hcd hco hdo).machine.Cfg)
    (coordBits : List Bool) (outBits : List N.Sym) (coordHead : ℕ) :
    (control N coord dim out hc hd ho hcd hco hdo).machine.Cfg where
  state := .fillZeros
  cells := fun i => if i = coord then N.tapeOf (coordBits.map N.bitSym)
    else if i = out then N.tapeOf (N.blank :: outBits) else c.cells i
  head := fun i => if i = coord then coordHead
    else if i = out then outBits.length + 2 else c.head i

private theorem blank_not_start (N : MultitapeTM) : N.blank ≠ N.startSym := by
  have hd := N.syms_distinct
  simp only [List.nodup_cons, List.mem_cons, not_or] at hd
  exact hd.1.1

private theorem tapeOf_update_at {N : MultitapeTM} (w : List N.Sym) (p : ℕ) :
    Function.update (N.tapeOf w) p ((N.tapeOf w) p) = N.tapeOf w := by
  funext i
  by_cases h : i = p
  · subst i
    simp
  · simp [Function.update_of_ne (Ne.symm h)]

private theorem tapeOf_blank_singleton (N : MultitapeTM) :
    N.tapeOf [N.blank] = N.tapeOf [] := by
  funext p
  cases p <;> simp [MultitapeTM.tapeOf]

private theorem bit_symbol_not_start (N : MultitapeTM) (b : Bool) :
    N.bitSym b ≠ N.startSym := by
  cases b
  · have hd := N.syms_distinct
    simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or] at hd
    exact Ne.symm hd.2.1.1
  · have hd := N.syms_distinct
    simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or] at hd
    exact Ne.symm hd.2.1.2.1

/-- The entry controller skips the sign and high bit while preserving the
    blank buffer prefix. -/
theorem skip_signed_prefix_run {N : MultitapeTM} (coord dim out : Fin N.k)
    (hc : coord ≠ N.inTape) (hd : dim ≠ N.inTape) (ho : out ≠ N.inTape)
    (hcd : coord ≠ dim) (hco : coord ≠ out) (hdo : dim ≠ out)
    (base : (control N coord dim out hc hd ho hcd hco hdo).machine.Cfg)
    (sign high : Bool) (low : List Bool) :
    (machine N coord dim out hc hd ho hcd hco hdo).step^[2]
      (BankedOperandStageProofSupport.initialStageFrame coord dim out hc hd ho hcd hco hdo base
        ([sign, high] ++ low)) =
      fillFrame coord dim out hc hd ho hcd hco hdo base
        ([sign, high] ++ low) [] 3 := by
  let P := control N coord dim out hc hd ho hcd hco hdo
  let c₀ := initialStageFrame coord dim out hc hd ho hcd hco hdo base
    ([sign, high] ++ low)
  let c₁ : P.machine.Cfg :=
    { state := State.skipHigh, cells := c₀.cells,
      head := fun i => if i = coord then 2 else if i = out then 2 else c₀.head i }
  have hstep₁ : (machine N coord dim out hc hd ho hcd hco hdo).step c₀ = c₁ := by
    apply cfg_ext P
    · rfl
    · funext i p
      by_cases hiC : i = coord
      · subst i
        simp [MultitapeTM.step, machine, c₀, c₁, initialStageFrame,
          OperandStage.control, transition, raw, protect_self_move, MultitapeTM.tapeOf]
        simpa [MultitapeTM.tapeOf] using congrArg (fun f : ℕ → N.Sym => f p)
          (tapeOf_update_at (N := N) ([N.bitSym sign, N.bitSym high] ++ low.map N.bitSym) 1)
      · by_cases hiO : i = out
        · subst i
          simp [MultitapeTM.step, machine, c₀, c₁, initialStageFrame,
            OperandStage.control, transition, raw, protect_self_move, MultitapeTM.tapeOf,
            Ne.symm hco]
          simpa [MultitapeTM.tapeOf, tapeOf_blank_singleton] using congrArg (fun f => f p)
            (tapeOf_update_at (N := N) [] 1)
        · simp [MultitapeTM.step, machine, c₀, c₁, initialStageFrame,
            OperandStage.control, transition, raw, protect_self_move, hiC, hiO]
    · funext i
      by_cases hiC : i = coord
      · subst i
        simp [MultitapeTM.step, machine, c₀, c₁, initialStageFrame,
          OperandStage.control, transition, raw, protect_self_move]
      · by_cases hiO : i = out
        · subst i
          simp [MultitapeTM.step, machine, c₀, c₁, initialStageFrame,
            OperandStage.control, transition, raw, protect_self_move, Ne.symm hco]
        · simp [MultitapeTM.step, machine, c₀, c₁, initialStageFrame,
            OperandStage.control, transition, raw, protect_self_move, hiC, hiO]
  have hstep₂ : (machine N coord dim out hc hd ho hcd hco hdo).step c₁ =
      fillFrame coord dim out hc hd ho hcd hco hdo base ([sign, high] ++ low) [] 3 := by
    apply cfg_ext P
    · rfl
    · funext i p
      by_cases hiC : i = coord
      · subst i
        simp [MultitapeTM.step, machine, c₁, c₀, fillFrame, initialStageFrame,
          OperandStage.control, transition, raw, protect_self_move, MultitapeTM.tapeOf]
        simpa [MultitapeTM.tapeOf] using congrArg (fun f : ℕ → N.Sym => f p)
          (tapeOf_update_at (N := N) ([N.bitSym sign, N.bitSym high] ++ low.map N.bitSym) 2)
      · by_cases hiO : i = out
        · subst i
          simp [MultitapeTM.step, machine, c₁, c₀, fillFrame, initialStageFrame,
            OperandStage.control, transition, raw, protect_self_move, MultitapeTM.tapeOf,
            Ne.symm hco]
          simpa [MultitapeTM.tapeOf, tapeOf_blank_singleton] using congrArg (fun f => f p)
            (tapeOf_update_at (N := N) [] 2)
        · simp [MultitapeTM.step, machine, c₁, c₀, fillFrame, initialStageFrame,
            OperandStage.control, transition, raw, protect_self_move, hiC, hiO]
    · funext i
      by_cases hiC : i = coord
      · subst i
        simp [MultitapeTM.step, machine, c₁, c₀, fillFrame, initialStageFrame,
          OperandStage.control, transition, raw, protect_self_move]
      · by_cases hiO : i = out
        · subst i
          simp [MultitapeTM.step, machine, c₁, c₀, fillFrame, initialStageFrame,
            OperandStage.control, transition, raw, protect_self_move, Ne.symm hco]
        · simp [MultitapeTM.step, machine, c₁, c₀, fillFrame, initialStageFrame,
            OperandStage.control, transition, raw, protect_self_move, hiC, hiO]
  have hiter : (machine N coord dim out hc hd ho hcd hco hdo).step^[2] c₀ =
      (machine N coord dim out hc hd ho hcd hco hdo).step
        ((machine N coord dim out hc hd ho hcd hco hdo).step c₀) := by
    simp [Function.iterate_succ_apply]
  rw [show initialStageFrame coord dim out hc hd ho hcd hco hdo base ([sign, high] ++ low) = c₀ by rfl,
    hiter, hstep₁, hstep₂]

private theorem rewind_nonmarker_transition {N : MultitapeTM}
    (coord dim out : Fin N.k) (a : Fin N.k → N.Sym)
    (hscan : a coord ≠ N.startSym) :
    transition N coord dim out .rewindCoordinate a =
      (.rewindCoordinate, fun i => (a i,
        if i = coord then .left else .stay)) := by
  apply Prod.ext
  · simp [transition, raw, hscan]
  · funext i
    by_cases hi : i = coord
    · subst i
      simp [transition, raw, hscan, protect]
    · simp [transition, raw, hi, hscan, protect_self_move]

private theorem rewind_marker_transition {N : MultitapeTM}
    (coord dim out : Fin N.k) (a : Fin N.k → N.Sym)
    (hscan : a coord = N.startSym) :
    transition N coord dim out .rewindCoordinate a =
      (.skipSignAgain, fun i => (a i,
        if i = coord then .right else .stay)) := by
  apply Prod.ext
  · simp [transition, raw, hscan]
  · funext i
    by_cases hi : i = coord
    · subst i
      simp [transition, raw, hscan, protect]
    · simp [transition, raw, hi, hscan, protect_self_move]

/-- In rewind state, a non-marker coordinate cell moves the coordinate head
    left and leaves every tape unchanged. -/
theorem rewind_nonmarker_step {N : MultitapeTM} (coord dim out : Fin N.k)
    (hc : coord ≠ N.inTape) (hd : dim ≠ N.inTape) (ho : out ≠ N.inTape)
    (hcd : coord ≠ dim) (hco : coord ≠ out) (hdo : dim ≠ out)
    (c : (control N coord dim out hc hd ho hcd hco hdo).machine.Cfg)
    (hs : c.state = State.rewindCoordinate)
    (hscan : c.cells coord (c.head coord) ≠ N.startSym) :
    (machine N coord dim out hc hd ho hcd hco hdo).step c =
      ⟨State.rewindCoordinate, c.cells,
        Function.update c.head coord (c.head coord - 1)⟩ := by
  let P := control N coord dim out hc hd ho hcd hco hdo
  have ht := rewind_nonmarker_transition coord dim out
    (fun i => c.cells i (c.head i)) hscan
  apply cfg_ext P
  · change (transition N coord dim out c.state
      (fun i => c.cells i (c.head i))).1 = State.rewindCoordinate
    rw [hs, ht]
  · funext i p
    change Function.update (c.cells i) (c.head i)
      (((transition N coord dim out c.state
        (fun j => c.cells j (c.head j))).2 i).1) p = c.cells i p
    rw [hs, ht]
    by_cases hp : p = c.head i <;> simp [hp]
  · funext i
    change (match ((transition N coord dim out c.state
        (fun j => c.cells j (c.head j))).2 i).2 with
      | Move.left => c.head i - 1
      | Move.stay => c.head i
      | Move.right => c.head i + 1) =
        Function.update c.head coord (c.head coord - 1) i
    rw [hs, ht]
    by_cases hi : i = coord <;> simp [hi]

/-- At coordinate cell zero, rewind exits into the sign-skip state and moves
    the head back to the first signed-record cell. -/
theorem rewind_marker_step {N : MultitapeTM} (coord dim out : Fin N.k)
    (hc : coord ≠ N.inTape) (hd : dim ≠ N.inTape) (ho : out ≠ N.inTape)
    (hcd : coord ≠ dim) (hco : coord ≠ out) (hdo : dim ≠ out)
    (c : (control N coord dim out hc hd ho hcd hco hdo).machine.Cfg)
    (hs : c.state = State.rewindCoordinate)
    (hscan : c.cells coord (c.head coord) = N.startSym) :
    (machine N coord dim out hc hd ho hcd hco hdo).step c =
      ⟨State.skipSignAgain, c.cells,
        Function.update c.head coord (c.head coord + 1)⟩ := by
  let P := control N coord dim out hc hd ho hcd hco hdo
  have ht := rewind_marker_transition coord dim out
    (fun i => c.cells i (c.head i)) hscan
  apply cfg_ext P
  · change (transition N coord dim out c.state
      (fun i => c.cells i (c.head i))).1 = State.skipSignAgain
    rw [hs, ht]
  · funext i p
    change Function.update (c.cells i) (c.head i)
      (((transition N coord dim out c.state
        (fun j => c.cells j (c.head j))).2 i).1) p = c.cells i p
    rw [hs, ht]
    by_cases hp : p = c.head i <;> simp [hp]
  · funext i
    change (match ((transition N coord dim out c.state
        (fun j => c.cells j (c.head j))).2 i).2 with
      | Move.left => c.head i - 1
      | Move.stay => c.head i
      | Move.right => c.head i + 1) =
        Function.update c.head coord (c.head coord + 1) i
    rw [hs, ht]
    by_cases hi : i = coord <;> simp [hi]

private def rewindFrame {N : MultitapeTM} (coord dim out : Fin N.k)
    (hc : coord ≠ N.inTape) (hd : dim ≠ N.inTape) (ho : out ≠ N.inTape)
    (hcd : coord ≠ dim) (hco : coord ≠ out) (hdo : dim ≠ out)
    (base : (control N coord dim out hc hd ho hcd hco hdo).machine.Cfg)
    (coordHead : ℕ) : (control N coord dim out hc hd ho hcd hco hdo).machine.Cfg where
  state := .rewindCoordinate
  cells := base.cells
  head := Function.update base.head coord coordHead

/-- A positive-length scan in rewind state returns to the marker, then exits
    with the coordinate head on the first signed-record symbol. -/
theorem rewind_coordinate_run {N : MultitapeTM} (coord dim out : Fin N.k)
    (hc : coord ≠ N.inTape) (hd : dim ≠ N.inTape) (ho : out ≠ N.inTape)
    (hcd : coord ≠ dim) (hco : coord ≠ out) (hdo : dim ≠ out)
    (base : (control N coord dim out hc hd ho hcd hco hdo).machine.Cfg)
    (p : ℕ) (hmarker : base.cells coord 0 = N.startSym)
    (hnonmarker : ∀ j, 1 ≤ j → base.cells coord j ≠ N.startSym) :
    (machine N coord dim out hc hd ho hcd hco hdo).step^[p + 1]
      (rewindFrame coord dim out hc hd ho hcd hco hdo base p) =
      ⟨State.skipSignAgain, base.cells,
        Function.update base.head coord 1⟩ := by
  induction p generalizing base with
  | zero =>
      have hstep := rewind_marker_step coord dim out hc hd ho hcd hco hdo
        (rewindFrame coord dim out hc hd ho hcd hco hdo base 0) rfl
        (by simpa [rewindFrame] using hmarker)
      simpa [rewindFrame] using hstep
  | succ p ih =>
      have hstep := rewind_nonmarker_step coord dim out hc hd ho hcd hco hdo
        (rewindFrame coord dim out hc hd ho hcd hco hdo base (p + 1)) rfl
        (by simpa [rewindFrame] using hnonmarker (p + 1) (by omega))
      have hframe :
          (machine N coord dim out hc hd ho hcd hco hdo).step
            (rewindFrame coord dim out hc hd ho hcd hco hdo base (p + 1)) =
          rewindFrame coord dim out hc hd ho hcd hco hdo base p := by
        simpa [rewindFrame] using hstep
      rw [show p + 1 + 1 = (p + 1) + 1 by omega, Function.iterate_add_apply]
      simp only [Function.iterate_one]
      rw [hframe]
      exact ih base hmarker hnonmarker

private theorem bits_tape_not_start {N : MultitapeTM} (w : List Bool) :
    ∀ p, 1 ≤ p → (N.tapeOf (w.map N.bitSym)) p ≠ N.startSym := by
  intro p hp
  cases p with
  | zero => omega
  | succ p =>
      change (w.map N.bitSym).getD p N.blank ≠ N.startSym
      rw [List.getD_eq_getElem?_getD, List.getElem?_map]
      by_cases hw : p < w.length
      · rw [List.getElem?_eq_getElem (by simpa using hw)]
        simp [bit_symbol_not_start]
      · rw [List.getElem?_eq_none (Nat.le_of_not_gt hw)]
        simp [blank_not_start]

private theorem fill_transition {N : MultitapeTM} (coord dim out : Fin N.k)
    (hc : coord ≠ N.inTape) (hd : dim ≠ N.inTape) (ho : out ≠ N.inTape)
    (hcd : coord ≠ dim) (hco : coord ≠ out) (hdo : dim ≠ out)
    (a : Fin N.k → N.Sym)
    (hbit : a coord = N.zero ∨ a coord = N.one)
    (hcoord : a coord ≠ N.startSym) (hout : a out ≠ N.startSym) :
    transition N coord dim out .fillZeros a =
      (.fillZeros, fun i =>
        (if i = out then N.zero else a i,
          if i = coord ∨ i = out then .right else .stay)) := by
  apply Prod.ext
  · simp [transition, raw, hbit]
  · have hzero : N.zero ≠ N.startSym := by
      intro h
      have hd := N.syms_distinct
      simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or] at hd
      exact hd.2.1.1 h.symm
    have hone : N.one ≠ N.startSym := by
      intro h
      have hd := N.syms_distinct
      simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or] at hd
      exact hd.2.1.2.1 h.symm
    funext i
    by_cases hiO : i = out
    · subst i
      simp [transition, raw, protect, hbit, hout, hzero]
    · by_cases hiC : i = coord
      · subst i
        simp [transition, raw, protect, hbit, hiO, hcoord, hzero, hone]
      · by_cases hm : a i = N.startSym
        · simp [transition, raw, protect, hbit, hiO, hiC, hm]
        · simp [transition, raw, protect, hbit, hiO, hiC, hm]

/-- When the coordinate clock reaches its blank terminator, switch from
    zero filling to the stored-dimension scan without changing any tape. -/
theorem fill_zeros_end_step {N : MultitapeTM} (coord dim out : Fin N.k)
    (hc : coord ≠ N.inTape) (hd : dim ≠ N.inTape) (ho : out ≠ N.inTape)
    (hcd : coord ≠ dim) (hco : coord ≠ out) (hdo : dim ≠ out)
    (c : (control N coord dim out hc hd ho hcd hco hdo).machine.Cfg)
    (hs : c.state = State.fillZeros)
    (hnonbit : c.cells coord (c.head coord) ≠ N.zero ∧
      c.cells coord (c.head coord) ≠ N.one) :
    (machine N coord dim out hc hd ho hcd hco hdo).step c =
      ⟨State.seekDimension, c.cells, c.head⟩ := by
  let P := control N coord dim out hc hd ho hcd hco hdo
  apply cfg_ext P
  · change (transition N coord dim out c.state
      (fun i => c.cells i (c.head i))).1 = State.seekDimension
    rw [hs]
    simp [transition, raw, hnonbit]
  · funext i p
    change Function.update (c.cells i) (c.head i)
      (((transition N coord dim out c.state
        (fun j => c.cells j (c.head j))).2 i).1) p = c.cells i p
    rw [hs]
    have hw : ((transition N coord dim out State.fillZeros
        (fun j => c.cells j (c.head j))).2 i).1 = c.cells i (c.head i) := by
      by_cases hi : i = coord
      · subst i
        simp [transition, raw, hnonbit, protect_self_move]
      · simp [transition, raw, hnonbit, hi, protect_self_move]
    rw [hw]
    by_cases hp : p = c.head i <;> simp [hp]
  · funext i
    change (match ((transition N coord dim out c.state
        (fun j => c.cells j (c.head j))).2 i).2 with
      | Move.left => c.head i - 1
      | Move.stay => c.head i
      | Move.right => c.head i + 1) = c.head i
    rw [hs]
    have hm : ((transition N coord dim out State.fillZeros
        (fun j => c.cells j (c.head j))).2 i).2 = Move.stay := by
      simp [transition, raw, hnonbit, protect_self_move]
    rw [hm]

/-- On a q-bit clock cell, one fill step writes a zero to the caller buffer
    and advances exactly the coordinate and buffer heads. -/
theorem fill_zero_step {N : MultitapeTM} (coord dim out : Fin N.k)
    (hc : coord ≠ N.inTape) (hd : dim ≠ N.inTape) (ho : out ≠ N.inTape)
    (hcd : coord ≠ dim) (hco : coord ≠ out) (hdo : dim ≠ out)
    (c : (control N coord dim out hc hd ho hcd hco hdo).machine.Cfg)
    (hs : c.state = State.fillZeros)
    (hbit : c.cells coord (c.head coord) = N.zero ∨
      c.cells coord (c.head coord) = N.one)
    (hcoord : c.cells coord (c.head coord) ≠ N.startSym)
    (hout : c.cells out (c.head out) ≠ N.startSym) :
    (machine N coord dim out hc hd ho hcd hco hdo).step c =
      ⟨State.fillZeros,
        fun i => if i = out then Function.update (c.cells i) (c.head i) N.zero
          else c.cells i,
        fun i => if i = coord ∨ i = out then c.head i + 1 else c.head i⟩ := by
  let P := control N coord dim out hc hd ho hcd hco hdo
  have ht := fill_transition coord dim out hc hd ho hcd hco hdo
    (fun i => c.cells i (c.head i)) hbit hcoord hout
  apply cfg_ext P
  · change (transition N coord dim out c.state
      (fun i => c.cells i (c.head i))).1 = State.fillZeros
    rw [hs, ht]
  · funext i p
    change Function.update (c.cells i) (c.head i)
      (((transition N coord dim out c.state
        (fun j => c.cells j (c.head j))).2 i).1) p = _
    rw [hs, ht]
    by_cases hi : i = out
    · subst i
      simp
    · simp [hi]
  · funext i
    change (match ((transition N coord dim out c.state
        (fun j => c.cells j (c.head j))).2 i).2 with
      | Move.left => c.head i - 1
      | Move.stay => c.head i
      | Move.right => c.head i + 1) = _
    rw [hs, ht]
    by_cases hi : i = coord
    · subst i
      simp [hco]
    · by_cases ho' : i = out
      · subst i
        simp [Ne.symm hco]
      · simp [hi, ho']

private theorem fill_frame_bit_step {N : MultitapeTM} (coord dim out : Fin N.k)
    (hc : coord ≠ N.inTape) (hd : dim ≠ N.inTape) (ho : out ≠ N.inTape)
    (hcd : coord ≠ dim) (hco : coord ≠ out) (hdo : dim ≠ out)
    (base : (control N coord dim out hc hd ho hcd hco hdo).machine.Cfg)
    (pre rest : List Bool) (b : Bool) (outBits : List N.Sym) :
    (machine N coord dim out hc hd ho hcd hco hdo).step
      (fillFrame coord dim out hc hd ho hcd hco hdo base
        (pre ++ b :: rest) outBits (pre.length + 1)) =
      fillFrame coord dim out hc hd ho hcd hco hdo base
        (pre ++ b :: rest) (outBits ++ [N.zero]) (pre.length + 2) := by
  let P := control N coord dim out hc hd ho hcd hco hdo
  let c := fillFrame coord dim out hc hd ho hcd hco hdo base
    (pre ++ b :: rest) outBits (pre.length + 1)
  have hscan : c.cells coord (c.head coord) = N.bitSym b := by
    simp [c, fillFrame, MultitapeTM.tapeOf, List.map_append, List.append_assoc]
  have hbit : c.cells coord (c.head coord) = N.zero ∨
      c.cells coord (c.head coord) = N.one := by
    rw [hscan]
    cases b <;> simp [MultitapeTM.bitSym]
  have hcoord : c.cells coord (c.head coord) ≠ N.startSym := by
    rcases hbit with hz | hone
    · rw [hz]
      have hd' := N.syms_distinct
      simp only [List.nodup_cons, List.mem_cons, not_or] at hd'
      exact Ne.symm hd'.2.1.1
    · rw [hone]
      have hd' := N.syms_distinct
      simp only [List.nodup_cons, List.mem_cons, not_or] at hd'
      exact Ne.symm hd'.2.1.2.1
  have hblank : c.cells out (c.head out) = N.blank := by
    simp [c, fillFrame, MultitapeTM.tapeOf, Ne.symm hco]
  have hblank_start : N.blank ≠ N.startSym := by
    have hd' := N.syms_distinct
    simp only [List.nodup_cons, List.mem_cons, not_or] at hd'
    exact hd'.1.1
  have hstep := fill_zero_step coord dim out hc hd ho hcd hco hdo c rfl
    hbit hcoord (by rw [hblank]; exact hblank_start)
  rw [hstep]
  apply cfg_ext P
  · rfl
  · funext i p
    by_cases hiO : i = out
    · subst i
      simp [c, fillFrame, Ne.symm hco]
      have happ := congrArg (fun f => f p) (tape_append N (N.blank :: outBits) N.zero)
      simpa [c, fillFrame, Ne.symm hco] using happ
    · by_cases hiC : i = coord
      · subst i
        simp [c, fillFrame, Ne.symm hco, hco]
      · simp [c, fillFrame, hiO, hiC]
  · funext i
    by_cases hiC : i = coord
    · subst i
      simp [c, fillFrame, Ne.symm hco, hco]
    · by_cases hiO : i = out
      · subst i
        simp [c, fillFrame, Ne.symm hco, hco]
      · simp [c, fillFrame, hiC, hiO]

/-- The controller writes one zero per low coordinate bit, without converting
    the precision q to unary: the q-bit coordinate itself is the clock. -/
theorem fill_zero_run {N : MultitapeTM} (coord dim out : Fin N.k)
    (hc : coord ≠ N.inTape) (hd : dim ≠ N.inTape) (ho : out ≠ N.inTape)
    (hcd : coord ≠ dim) (hco : coord ≠ out) (hdo : dim ≠ out)
    (base : (control N coord dim out hc hd ho hcd hco hdo).machine.Cfg)
    (pre rest : List Bool) (outBits : List N.Sym) :
    (machine N coord dim out hc hd ho hcd hco hdo).step^[rest.length]
      (fillFrame coord dim out hc hd ho hcd hco hdo base
        (pre ++ rest) outBits (pre.length + 1)) =
      fillFrame coord dim out hc hd ho hcd hco hdo base
        (pre ++ rest) (outBits ++ List.replicate rest.length N.zero)
        (pre.length + rest.length + 1) := by
  induction rest generalizing pre outBits with
  | nil => simp [fillFrame]
  | cons b rest ih =>
      rw [List.length_cons, Function.iterate_succ_apply, fill_frame_bit_step]
      have htail := ih (pre ++ [b]) (outBits ++ [N.zero])
      simpa [List.length_append, List.append_assoc, List.replicate_succ,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail

private def seekAfterFillFrame {N : MultitapeTM} (coord dim out : Fin N.k)
    (hc : coord ≠ N.inTape) (hd : dim ≠ N.inTape) (ho : out ≠ N.inTape)
    (hcd : coord ≠ dim) (hco : coord ≠ out) (hdo : dim ≠ out)
    (base : (control N coord dim out hc hd ho hcd hco hdo).machine.Cfg)
    (source : List Bool) (outBits : List N.Sym) (coordHead : ℕ) :
    (control N coord dim out hc hd ho hcd hco hdo).machine.Cfg where
  state := .seekDimension
  cells := fun i => if i = coord then N.tapeOf (source.map N.bitSym)
    else if i = out then N.tapeOf (N.blank :: outBits) else base.cells i
  head := fun i => if i = coord then coordHead
    else if i = out then outBits.length + 2 else base.head i

private theorem fill_frame_end_step {N : MultitapeTM} (coord dim out : Fin N.k)
    (hc : coord ≠ N.inTape) (hd : dim ≠ N.inTape) (ho : out ≠ N.inTape)
    (hcd : coord ≠ dim) (hco : coord ≠ out) (hdo : dim ≠ out)
    (base : (control N coord dim out hc hd ho hcd hco hdo).machine.Cfg)
    (source : List Bool) (outBits : List N.Sym) :
    (machine N coord dim out hc hd ho hcd hco hdo).step
      (fillFrame coord dim out hc hd ho hcd hco hdo base source outBits
        (source.length + 1)) =
      seekAfterFillFrame coord dim out hc hd ho hcd hco hdo base source outBits
        (source.length + 1) := by
  have hblank : (fillFrame coord dim out hc hd ho hcd hco hdo base source outBits
      (source.length + 1)).cells coord
        ((fillFrame coord dim out hc hd ho hcd hco hdo base source outBits
          (source.length + 1)).head coord) = N.blank := by
    simp [fillFrame, MultitapeTM.tapeOf]
  have hnonbit :
      (fillFrame coord dim out hc hd ho hcd hco hdo base source outBits
        (source.length + 1)).cells coord
        ((fillFrame coord dim out hc hd ho hcd hco hdo base source outBits
          (source.length + 1)).head coord) ≠ N.zero ∧
      (fillFrame coord dim out hc hd ho hcd hco hdo base source outBits
        (source.length + 1)).cells coord
        ((fillFrame coord dim out hc hd ho hcd hco hdo base source outBits
          (source.length + 1)).head coord) ≠ N.one := by
    rw [hblank]
    have hz : N.blank ≠ N.zero := by
      intro h
      have hnot := (List.nodup_cons.mp N.syms_distinct).1
      exact hnot (by simp [h])
    have ho : N.blank ≠ N.one := by
      intro h
      have hnot := (List.nodup_cons.mp N.syms_distinct).1
      exact hnot (by simp [h])
    exact ⟨hz, ho⟩
  have hstep := fill_zeros_end_step coord dim out hc hd ho hcd hco hdo
    (fillFrame coord dim out hc hd ho hcd hco hdo base source outBits
      (source.length + 1)) rfl hnonbit
  simpa [seekAfterFillFrame, fillFrame] using hstep

/-- Skip the signed-record prefix, write one leading-zero candidate per low
    coordinate bit, then enter the dimension scan at the exact buffer frame. -/
theorem signed_fill_seek_run {N : MultitapeTM} (coord dim out : Fin N.k)
    (hc : coord ≠ N.inTape) (hd : dim ≠ N.inTape) (ho : out ≠ N.inTape)
    (hcd : coord ≠ dim) (hco : coord ≠ out) (hdo : dim ≠ out)
    (base : (control N coord dim out hc hd ho hcd hco hdo).machine.Cfg)
    (sign high : Bool) (low : List Bool) :
    (machine N coord dim out hc hd ho hcd hco hdo).step^[low.length + 3]
      (initialStageFrame coord dim out hc hd ho hcd hco hdo base
        ([sign, high] ++ low)) =
      seekAfterFillFrame coord dim out hc hd ho hcd hco hdo base
        ([sign, high] ++ low) (List.replicate low.length N.zero) (low.length + 3) := by
  let source := [sign, high] ++ low
  have hskip := skip_signed_prefix_run coord dim out hc hd ho hcd hco hdo
    base sign high low
  have hfill := fill_zero_run coord dim out hc hd ho hcd hco hdo base
    [sign, high] low []
  have hterm := fill_frame_end_step coord dim out hc hd ho hcd hco hdo base
    source (List.replicate low.length N.zero)
  have hcompose :
      (machine N coord dim out hc hd ho hcd hco hdo).step^[low.length + 2]
        (initialStageFrame coord dim out hc hd ho hcd hco hdo base source) =
      fillFrame coord dim out hc hd ho hcd hco hdo base source
        (List.replicate low.length N.zero) (low.length + 3) := by
    rw [Function.iterate_add_apply]
    dsimp only [source]
    rw [hskip]
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hfill
  rw [show low.length + 3 = (low.length + 2) + 1 by omega,
    Function.iterate_succ_apply', hcompose]
  simpa [source] using hterm

/-- Scanning a bit of the stored dimension advances only its read head. -/
theorem seek_dimension_bit_step {N : MultitapeTM} (coord dim out : Fin N.k)
    (hc : coord ≠ N.inTape) (hd : dim ≠ N.inTape) (ho : out ≠ N.inTape)
    (hcd : coord ≠ dim) (hco : coord ≠ out) (hdo : dim ≠ out)
    (c : (control N coord dim out hc hd ho hcd hco hdo).machine.Cfg)
    (hs : c.state = State.seekDimension)
    (hbit : c.cells dim (c.head dim) = N.zero ∨
      c.cells dim (c.head dim) = N.one) :
    (machine N coord dim out hc hd ho hcd hco hdo).step c =
      ⟨State.seekDimension, c.cells,
        Function.update c.head dim (c.head dim + 1)⟩ := by
  let P := control N coord dim out hc hd ho hcd hco hdo
  apply cfg_ext P
  · change (transition N coord dim out c.state
      (fun i => c.cells i (c.head i))).1 = State.seekDimension
    rw [hs]
    simp [transition, raw, hbit]
  · funext i p
    change Function.update (c.cells i) (c.head i)
      (((transition N coord dim out c.state
        (fun j => c.cells j (c.head j))).2 i).1) p = c.cells i p
    rw [hs]
    have hw : ((transition N coord dim out State.seekDimension
        (fun j => c.cells j (c.head j))).2 i).1 = c.cells i (c.head i) := by
      by_cases hi : i = dim
      · subst i
        simp [transition, raw, hbit, protect_self_move]
      · simp [transition, raw, hbit, hi, protect_self_move]
    rw [hw]
    by_cases hp : p = c.head i <;> simp [hp]
  · funext i
    change (match ((transition N coord dim out c.state
        (fun j => c.cells j (c.head j))).2 i).2 with
      | Move.left => c.head i - 1
      | Move.stay => c.head i
      | Move.right => c.head i + 1) = _
    rw [hs]
    have hm : ((transition N coord dim out State.seekDimension
        (fun j => c.cells j (c.head j))).2 i).2 =
        if i = dim then Move.right else Move.stay := by
      by_cases hi : i = dim <;> simp [transition, raw, hbit, hi, protect_self_move]
    rw [hm]
    by_cases hi : i = dim <;> simp [hi]

private def seekFrame {N : MultitapeTM} (coord dim out : Fin N.k)
    (hc : coord ≠ N.inTape) (hd : dim ≠ N.inTape) (ho : out ≠ N.inTape)
    (hcd : coord ≠ dim) (hco : coord ≠ out) (hdo : dim ≠ out)
    (base : (control N coord dim out hc hd ho hcd hco hdo).machine.Cfg)
    (dimension : List Bool) (outBits : List N.Sym)
    (dimensionHead outHead : ℕ) :
    (control N coord dim out hc hd ho hcd hco hdo).machine.Cfg where
  state := .seekDimension
  cells := fun i => if i = dim then N.tapeOf (dimension.map N.bitSym)
    else if i = out then N.tapeOf (N.blank :: outBits) else base.cells i
  head := fun i => if i = dim then dimensionHead
    else if i = out then outHead else base.head i

private theorem seek_frame_bit_step {N : MultitapeTM} (coord dim out : Fin N.k)
    (hc : coord ≠ N.inTape) (hd : dim ≠ N.inTape) (ho : out ≠ N.inTape)
    (hcd : coord ≠ dim) (hco : coord ≠ out) (hdo : dim ≠ out)
    (base : (control N coord dim out hc hd ho hcd hco hdo).machine.Cfg)
    (pre rest : List Bool) (b : Bool) (outBits : List N.Sym)
    (outHead : ℕ) :
    (machine N coord dim out hc hd ho hcd hco hdo).step
      (seekFrame coord dim out hc hd ho hcd hco hdo base
        (pre ++ b :: rest) outBits (pre.length + 1) outHead) =
      seekFrame coord dim out hc hd ho hcd hco hdo base
        (pre ++ b :: rest) outBits (pre.length + 2) outHead := by
  let P := control N coord dim out hc hd ho hcd hco hdo
  let c := seekFrame coord dim out hc hd ho hcd hco hdo base
    (pre ++ b :: rest) outBits (pre.length + 1) outHead
  have hscan : c.cells dim (c.head dim) = N.bitSym b := by
    simp [c, seekFrame, MultitapeTM.tapeOf, List.map_append, List.append_assoc]
  have hbit : c.cells dim (c.head dim) = N.zero ∨
      c.cells dim (c.head dim) = N.one := by
    rw [hscan]
    cases b <;> simp [MultitapeTM.bitSym]
  have hstep := seek_dimension_bit_step coord dim out hc hd ho hcd hco hdo
    c rfl hbit
  rw [hstep]
  apply cfg_ext P
  · rfl
  · funext i p
    simp [c, seekFrame, hco, Ne.symm hco]
  · funext i
    by_cases hiD : i = dim
    · subst i
      simp [c, seekFrame, Ne.symm hcd, Ne.symm hdo]
    · by_cases hiO : i = out
      · subst i
        simp [c, seekFrame, Ne.symm hco, Ne.symm hdo]
      · simp [c, seekFrame, hiD, hiO]

/-- A left-to-right scan of the stored binary dimension takes exactly its bit
    length and does not touch the caller buffer or coordinate source. -/
theorem seek_dimension_run {N : MultitapeTM} (coord dim out : Fin N.k)
    (hc : coord ≠ N.inTape) (hd : dim ≠ N.inTape) (ho : out ≠ N.inTape)
    (hcd : coord ≠ dim) (hco : coord ≠ out) (hdo : dim ≠ out)
    (base : (control N coord dim out hc hd ho hcd hco hdo).machine.Cfg)
    (pre rest : List Bool) (outBits : List N.Sym) (outHead : ℕ) :
    (machine N coord dim out hc hd ho hcd hco hdo).step^[rest.length]
      (seekFrame coord dim out hc hd ho hcd hco hdo base
        (pre ++ rest) outBits (pre.length + 1) outHead) =
      seekFrame coord dim out hc hd ho hcd hco hdo base
        (pre ++ rest) outBits (pre.length + rest.length + 1) outHead := by
  induction rest generalizing pre with
  | nil => simp [seekFrame]
  | cons b rest ih =>
      rw [List.length_cons, Function.iterate_succ_apply, seek_frame_bit_step]
      have htail := ih (pre ++ [b])
      simpa [List.length_append, List.append_assoc, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using htail

private theorem seek_blank_transition {N : MultitapeTM} (coord dim out : Fin N.k)
    (a : Fin N.k → N.Sym)
    (hnonbit : a dim ≠ N.zero ∧ a dim ≠ N.one)
    (hdim : a dim ≠ N.startSym) (hout : a out ≠ N.startSym) :
    transition N coord dim out .seekDimension a =
      (.copyDimensionBackward, fun i =>
        (a i, if i = dim ∨ i = out then .left else .stay)) := by
  apply Prod.ext
  · simp [transition, raw, hnonbit]
  · have hz : N.zero ≠ N.startSym := by
      intro h
      have hs := N.syms_distinct
      simp only [List.nodup_cons, List.mem_cons, not_or] at hs
      exact Ne.symm hs.2.1.1 h
    have ho' : N.one ≠ N.startSym := by
      intro h
      have hs := N.syms_distinct
      simp only [List.nodup_cons, List.mem_cons, not_or] at hs
      exact Ne.symm hs.2.1.2.1 h
    funext i
    by_cases hiD : i = dim
    · subst i
      simp [transition, raw, hnonbit, protect, hdim]
    · by_cases hiO : i = out
      · subst i
        simp [transition, raw, hnonbit, protect, hout]
      · by_cases hm : a i = N.startSym
        · simp [transition, raw, hnonbit, hiD, hiO, protect, hm]
        · simp [transition, raw, hnonbit, hiD, hiO, protect, hm]

/-- At the blank immediately following the dimension, the scan enters the
    reverse-copy state and backs up both the dimension and output heads once. -/
theorem seek_dimension_end_step {N : MultitapeTM} (coord dim out : Fin N.k)
    (hc : coord ≠ N.inTape) (hd : dim ≠ N.inTape) (ho : out ≠ N.inTape)
    (hcd : coord ≠ dim) (hco : coord ≠ out) (hdo : dim ≠ out)
    (c : (control N coord dim out hc hd ho hcd hco hdo).machine.Cfg)
    (hs : c.state = State.seekDimension)
    (hnonbit : c.cells dim (c.head dim) ≠ N.zero ∧
      c.cells dim (c.head dim) ≠ N.one)
    (hdim : c.cells dim (c.head dim) ≠ N.startSym)
    (hout : c.cells out (c.head out) ≠ N.startSym)
    (hhd : 1 ≤ c.head dim) (hho : 1 ≤ c.head out) :
    (machine N coord dim out hc hd ho hcd hco hdo).step c =
      ⟨State.copyDimensionBackward, c.cells,
        fun i => if i = dim ∨ i = out then c.head i - 1 else c.head i⟩ := by
  let P := control N coord dim out hc hd ho hcd hco hdo
  have ht := seek_blank_transition coord dim out
    (fun i => c.cells i (c.head i)) hnonbit hdim hout
  apply cfg_ext P
  · change (transition N coord dim out c.state
      (fun i => c.cells i (c.head i))).1 = State.copyDimensionBackward
    rw [hs, ht]
  · funext i p
    change Function.update (c.cells i) (c.head i)
      (((transition N coord dim out c.state
        (fun j => c.cells j (c.head j))).2 i).1) p = c.cells i p
    rw [hs, ht]
    by_cases hp : p = c.head i <;> simp [hp]
  · funext i
    change (match ((transition N coord dim out c.state
        (fun j => c.cells j (c.head j))).2 i).2 with
      | Move.left => c.head i - 1
      | Move.stay => c.head i
      | Move.right => c.head i + 1) = _
    rw [hs, ht]
    by_cases hiD : i = dim
    · subst i
      simp [hhd]
    · by_cases hiO : i = out
      · subst i
        simp [hho]
      · simp [hiD, hiO]

private theorem copy_backward_transition {N : MultitapeTM}
    (coord dim out : Fin N.k) (a : Fin N.k → N.Sym)
    (hbit : a dim = N.zero ∨ a dim = N.one)
    (hdim : a dim ≠ N.startSym) (hout : a out ≠ N.startSym) :
    transition N coord dim out .copyDimensionBackward a =
      (.copyDimensionBackward, fun i =>
        (if i = out then a dim else a i,
          if i = dim ∨ i = out then .left else .stay)) := by
  apply Prod.ext
  · simp [transition, raw, hbit]
  · funext i
    by_cases hiO : i = out
    · subst i
      simp [transition, raw, protect, hbit, hdim, hout]
    · by_cases hiD : i = dim
      · subst i
        simp [transition, raw, protect, hbit, hiO, hdim]
      · by_cases hm : a i = N.startSym
        · simp [transition, raw, protect, hbit, hiO, hiD, hm]
        · simp [transition, raw, protect, hbit, hiO, hiD, hm]

/-- One reverse-copy step writes the scanned dimension bit over the current
    zero slot and moves both heads left. -/
theorem copy_backward_bit_step {N : MultitapeTM} (coord dim out : Fin N.k)
    (hc : coord ≠ N.inTape) (hd : dim ≠ N.inTape) (ho : out ≠ N.inTape)
    (hcd : coord ≠ dim) (hco : coord ≠ out) (hdo : dim ≠ out)
    (c : (control N coord dim out hc hd ho hcd hco hdo).machine.Cfg)
    (hs : c.state = State.copyDimensionBackward)
    (hbit : c.cells dim (c.head dim) = N.zero ∨
      c.cells dim (c.head dim) = N.one)
    (hdim : c.cells dim (c.head dim) ≠ N.startSym)
    (hout : c.cells out (c.head out) ≠ N.startSym) :
    (machine N coord dim out hc hd ho hcd hco hdo).step c =
      ⟨State.copyDimensionBackward,
        fun i => if i = out then Function.update (c.cells i) (c.head i)
          (c.cells dim (c.head dim)) else c.cells i,
        fun i => if i = dim ∨ i = out then c.head i - 1 else c.head i⟩ := by
  let P := control N coord dim out hc hd ho hcd hco hdo
  have ht := copy_backward_transition coord dim out
    (fun i => c.cells i (c.head i)) hbit hdim hout
  apply cfg_ext P
  · change (transition N coord dim out c.state
      (fun i => c.cells i (c.head i))).1 = State.copyDimensionBackward
    rw [hs, ht]
  · funext i p
    change Function.update (c.cells i) (c.head i)
      (((transition N coord dim out c.state
        (fun j => c.cells j (c.head j))).2 i).1) p = _
    rw [hs, ht]
    by_cases hi : i = out
    · subst i
      simp
    · simp [hi]
  · funext i
    change (match ((transition N coord dim out c.state
        (fun j => c.cells j (c.head j))).2 i).2 with
      | Move.left => c.head i - 1
      | Move.stay => c.head i
      | Move.right => c.head i + 1) = _
    rw [hs, ht]
    by_cases hi : i = dim
    · subst i
      simp
    · by_cases ho' : i = out
      · subst i
        simp
      · simp [hi, ho']

private def copyFrame {N : MultitapeTM} (coord dim out : Fin N.k)
    (hc : coord ≠ N.inTape) (hd : dim ≠ N.inTape) (ho : out ≠ N.inTape)
    (hcd : coord ≠ dim) (hco : coord ≠ out) (hdo : dim ≠ out)
    (base : (control N coord dim out hc hd ho hcd hco hdo).machine.Cfg)
    (remaining : List Bool) (outCells : ℕ → N.Sym) (outHead : ℕ) :
    (control N coord dim out hc hd ho hcd hco hdo).machine.Cfg where
  state := .copyDimensionBackward
  cells := fun i => if i = out then outCells else base.cells i
  head := fun i => if i = dim then remaining.length
    else if i = out then outHead else base.head i

private def writeReverse {N : MultitapeTM} (outCells : ℕ → N.Sym) :
    List Bool → ℕ → ℕ → N.Sym
  | [], _ => outCells
  | b :: rest, pos => writeReverse
      (Function.update outCells pos (N.bitSym b)) rest (pos - 1)

private theorem bitSym_ne_start {N : MultitapeTM} (b : Bool) :
    N.bitSym b ≠ N.startSym := by
  cases b <;> simp [MultitapeTM.bitSym]
  all_goals
    have hd := N.syms_distinct
    simp only [List.nodup_cons, List.mem_cons, not_or] at hd
    first | exact Ne.symm hd.2.1.1 | exact Ne.symm hd.2.1.2.1

private theorem start_ne_zero {N : MultitapeTM} : N.startSym ≠ N.zero := by
  intro h
  have hnot := (List.nodup_cons.mp N.syms_distinct).2
  have hnot := (List.nodup_cons.mp hnot).1
  exact hnot (by simp [h])

private theorem start_ne_one {N : MultitapeTM} : N.startSym ≠ N.one := by
  intro h
  have hnot := (List.nodup_cons.mp N.syms_distinct).2
  have hnot := (List.nodup_cons.mp hnot).1
  exact hnot (by simp [h])

private theorem blank_ne_zero {N : MultitapeTM} : N.blank ≠ N.zero := by
  intro h
  have hnot := (List.nodup_cons.mp N.syms_distinct).1
  exact hnot (by simp [h])

private theorem blank_ne_start {N : MultitapeTM} : N.blank ≠ N.startSym := by
  intro h
  have hnot := (List.nodup_cons.mp N.syms_distinct).1
  exact hnot (by simp [h])

private theorem blank_ne_one {N : MultitapeTM} : N.blank ≠ N.one := by
  intro h
  have hnot := (List.nodup_cons.mp N.syms_distinct).1
  exact hnot (by simp [h])

private theorem sep_ne_start {N : MultitapeTM} : N.sep ≠ N.startSym := by
  intro h
  have hnot := (List.nodup_cons.mp N.syms_distinct).2
  have hnot := (List.nodup_cons.mp hnot).1
  exact hnot (by simp [h])

private theorem writeReverse_nonmarker {N : MultitapeTM} (outCells : ℕ → N.Sym)
    (bits : List Bool) (pos : ℕ)
    (hroom : bits.length ≤ pos)
    (hout : ∀ p, 1 ≤ p → outCells p ≠ N.startSym) :
    ∀ p, 1 ≤ p → writeReverse outCells bits pos p ≠ N.startSym := by
  induction bits generalizing outCells pos with
  | nil => simpa [writeReverse] using hout
  | cons b bits ih =>
      have hpos : 1 ≤ pos := by simp only [List.length_cons] at hroom; omega
      have hnew : ∀ p, 1 ≤ p → Function.update outCells pos (N.bitSym b) p ≠ N.startSym := by
        intro p hp
        by_cases he : p = pos
        · subst p
          simp [Function.update_eq_self, bitSym_ne_start]
        · simp [Function.update_of_ne, he]
          exact hout p hp
      have htail : bits.length ≤ pos - 1 := by simp only [List.length_cons] at hroom; omega
      exact ih (Function.update outCells pos (N.bitSym b)) (pos - 1) htail hnew

private theorem update_tape_middle {N : MultitapeTM} (pre post : List N.Sym)
    (old new : N.Sym) :
    Function.update (N.tapeOf (pre ++ old :: post)) (pre.length + 1) new =
      N.tapeOf (pre ++ new :: post) := by
  funext p
  cases p with
  | zero => simp [MultitapeTM.tapeOf]
  | succ p =>
      by_cases hp : p = pre.length
      · subst p
        simp [MultitapeTM.tapeOf]
      · rw [Function.update_of_ne (by omega : p + 1 ≠ pre.length + 1)]
        simp only [MultitapeTM.tapeOf]
        by_cases hpre : p < pre.length
        · rw [List.getD_append _ _ _ _ hpre, List.getD_append _ _ _ _ hpre]
        · have hpost : pre.length < p := by omega
          rw [List.getD_append_right _ _ _ _ (Nat.le_of_lt hpost),
            List.getD_append_right _ _ _ _ (Nat.le_of_lt hpost)]
          have hidx : 0 < p - pre.length := by omega
          cases hidx' : p - pre.length with
          | zero => omega
          | succ i => simp [hidx']

/-- Reverse copying `bits` into the rightmost cells of a zero-padded word gives
    the zero-padded bit encoding, while preserving any cells after that word. -/
theorem writeReverse_zero_pad {N : MultitapeTM} (bits : List Bool)
    (padding : ℕ) (tail : List N.Sym) :
    writeReverse
        (N.tapeOf (N.blank :: List.replicate (padding + bits.length) N.zero ++ tail))
        bits.reverse (padding + bits.length + 1) =
      N.tapeOf (N.blank :: List.replicate padding N.zero ++
        bits.map N.bitSym ++ tail) := by
  induction bits using List.reverseRecOn generalizing padding tail with
  | nil => simp [writeReverse, MultitapeTM.tapeOf]
  | append_singleton pre b ih =>
      have hpad : 0 < padding + (pre ++ [b]).length := by simp only [List.length_append, List.length_singleton]; omega
      have hbase : N.blank :: List.replicate (padding + (pre.length + 1)) N.zero ++ tail =
          (N.blank :: List.replicate (padding + pre.length) N.zero) ++ N.zero :: tail := by
        rw [show padding + (pre.length + 1) = (padding + pre.length) + 1 by omega,
          List.replicate_add]
        simp [List.append_assoc]
      rw [show (pre ++ [b]).reverse = b :: pre.reverse by simp]
      simp only [List.length_append, List.length_singleton]
      rw [writeReverse]
      rw [hbase]
      have hpos : padding + (pre.length + 1) + 1 =
          (N.blank :: List.replicate (padding + pre.length) N.zero).length + 1 := by
        simp
        omega
      rw [hpos, update_tape_middle]
      have htail := ih padding (N.bitSym b :: tail)
      simpa [List.length_append, List.length_singleton, List.map_append,
        List.append_assoc, List.replicate_succ, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using htail

private theorem copy_frame_bit_step {N : MultitapeTM} (coord dim out : Fin N.k)
    (hc : coord ≠ N.inTape) (hd : dim ≠ N.inTape) (ho : out ≠ N.inTape)
    (hcd : coord ≠ dim) (hco : coord ≠ out) (hdo : dim ≠ out)
    (base : (control N coord dim out hc hd ho hcd hco hdo).machine.Cfg)
    (pre : List Bool) (b : Bool) (outCells : ℕ → N.Sym) (outHead : ℕ)
    (hscan : base.cells dim (pre.length + 1) = N.bitSym b)
    (hout : outCells outHead ≠ N.startSym) :
    (machine N coord dim out hc hd ho hcd hco hdo).step
      (copyFrame coord dim out hc hd ho hcd hco hdo base
        (pre ++ [b]) outCells outHead) =
      copyFrame coord dim out hc hd ho hcd hco hdo base pre
        (Function.update outCells outHead (N.bitSym b)) (outHead - 1) := by
  let P := control N coord dim out hc hd ho hcd hco hdo
  let c := copyFrame coord dim out hc hd ho hcd hco hdo base
    (pre ++ [b]) outCells outHead
  have hscan' : c.cells dim (c.head dim) = N.bitSym b := by
    simpa [c, copyFrame, hdo] using hscan
  have hbit : c.cells dim (c.head dim) = N.zero ∨
      c.cells dim (c.head dim) = N.one := by
    rw [hscan']
    cases b <;> simp [MultitapeTM.bitSym]
  have hsource : c.cells dim (c.head dim) ≠ N.startSym := by
    rw [hscan']
    exact bitSym_ne_start b
  have hout' : c.cells out (c.head out) ≠ N.startSym := by
    simpa [c, copyFrame, Ne.symm hdo] using hout
  have hstep := copy_backward_bit_step coord dim out hc hd ho hcd hco hdo
    c rfl hbit hsource hout'
  rw [hstep]
  apply cfg_ext P
  · rfl
  · funext i p
    by_cases hiO : i = out
    · subst i
      rw [hscan']
      simp [c, copyFrame, Ne.symm hco, Ne.symm hdo]
    · by_cases hiD : i = dim
      · subst i
        simp [c, copyFrame, hco, Ne.symm hco, hdo, Ne.symm hdo]
      · simp [c, copyFrame, hiO, hiD]
  · funext i
    by_cases hiD : i = dim
    · subst i
      simp [c, copyFrame, Ne.symm hco, hdo]
    · by_cases hiO : i = out
      · subst i
        simp [c, copyFrame, Ne.symm hco, Ne.symm hdo]
      · simp [c, copyFrame, hiD, hiO]

/-- Exact run of the reverse copy. The `remaining` bits form a prefix of the
    immutable dimension tape; each step writes its last bit into the next zero
    slot moving from right to left. -/
theorem copy_dimension_run {N : MultitapeTM} (coord dim out : Fin N.k)
    (hc : coord ≠ N.inTape) (hd : dim ≠ N.inTape) (ho : out ≠ N.inTape)
    (hcd : coord ≠ dim) (hco : coord ≠ out) (hdo : dim ≠ out)
    (base : (control N coord dim out hc hd ho hcd hco hdo).machine.Cfg)
    (source remaining : List Bool) (outCells : ℕ → N.Sym) (outHead : ℕ)
    (hsource : base.cells dim = N.tapeOf (source.map N.bitSym))
    (hprefix : ∃ suffix, source = remaining ++ suffix)
    (hroom : remaining.length ≤ outHead)
    (hout : ∀ p, 1 ≤ p → outCells p ≠ N.startSym) :
    (machine N coord dim out hc hd ho hcd hco hdo).step^[remaining.length]
      (copyFrame coord dim out hc hd ho hcd hco hdo base remaining outCells outHead) =
      copyFrame coord dim out hc hd ho hcd hco hdo base []
        (writeReverse outCells remaining.reverse outHead)
        (outHead - remaining.length) := by
  induction remaining using List.reverseRecOn generalizing source outCells outHead with
  | nil => simp [copyFrame, writeReverse]
  | append_singleton pre b ih =>
      obtain ⟨suffix, hs⟩ := hprefix
      have hroom' : (pre ++ [b]).length ≤ outHead := by simpa using hroom
      have hpos : 1 ≤ outHead := by simp only [List.length_append, List.length_singleton] at hroom'; omega
      have hscan : base.cells dim (pre.length + 1) = N.bitSym b := by
        rw [hsource, hs]
        simp [MultitapeTM.tapeOf, List.map_append, List.append_assoc]
      have hprefix' : ∃ tail, source = pre ++ tail := by
        refine ⟨b :: suffix, ?_⟩
        simpa [List.append_assoc] using hs
      have hnew : ∀ p, 1 ≤ p → Function.update outCells outHead
          (N.bitSym b) p ≠ N.startSym := by
        intro p hp
        by_cases he : p = outHead
        · subst p
          simp [Function.update_eq_self, bitSym_ne_start]
        · simp [Function.update_of_ne, he]
          exact hout p hp
      have hroomTail : pre.length ≤ outHead - 1 := by
        simp only [List.length_append, List.length_singleton] at hroom'
        omega
      rw [List.length_append, List.length_singleton, Function.iterate_succ_apply,
        copy_frame_bit_step coord dim out hc hd ho hcd hco hdo base pre b outCells
          outHead hscan (hout outHead hpos)]
      have htail := ih source
        (Function.update outCells outHead (N.bitSym b)) (outHead - 1)
        hsource hprefix' hroomTail hnew
      have hwrite : writeReverse outCells (b :: pre.reverse) outHead =
          writeReverse (Function.update outCells outHead (N.bitSym b))
            pre.reverse (outHead - 1) := by
        rfl
      have hhead : outHead - 1 - pre.length = outHead - (pre.length + 1) := by omega
      simpa [List.reverse_append, hwrite, hhead] using htail

/-- Starting from `q` zero slots, the reverse-copy phase writes the parsed
    dimension as the first multiplier operand `bin q n`, including leading
    zero padding, and leaves the output head at the end of that operand. -/
theorem copy_dimension_zero_padded {N : MultitapeTM} (coord dim out : Fin N.k)
    (hc : coord ≠ N.inTape) (hd : dim ≠ N.inTape) (ho : out ≠ N.inTape)
    (hcd : coord ≠ dim) (hco : coord ≠ out) (hdo : dim ≠ out)
    (base : (control N coord dim out hc hd ho hcd hco hdo).machine.Cfg)
    (source : List Bool) (q : ℕ)
    (hsource : base.cells dim = N.tapeOf (source.map N.bitSym))
    (hout : ∀ p, 1 ≤ p → (N.tapeOf (N.blank :: List.replicate q N.zero)) p ≠ N.startSym)
    (hq : source.length ≤ q) :
    (machine N coord dim out hc hd ho hcd hco hdo).step^[source.length]
      (copyFrame coord dim out hc hd ho hcd hco hdo base source
        (N.tapeOf (N.blank :: List.replicate q N.zero)) (q + 1)) =
      copyFrame coord dim out hc hd ho hcd hco hdo base []
        (N.tapeOf (N.blank :: List.replicate (q - source.length) N.zero ++
          source.map N.bitSym)) (q + 1 - source.length) := by
  have hrun := copy_dimension_run coord dim out hc hd ho hcd hco hdo base
    source source (N.tapeOf (N.blank :: List.replicate q N.zero)) (q + 1)
    hsource ⟨[], by simp⟩ (by omega) hout
  rw [hrun]
  have hpad : (q - source.length) + source.length = q := Nat.sub_add_cancel hq
  have hwrite : writeReverse (N.tapeOf (N.blank :: List.replicate q N.zero))
      source.reverse (q + 1) =
      N.tapeOf (N.blank :: List.replicate (q - source.length) N.zero ++
        source.map N.bitSym) := by
    simpa [hpad] using (writeReverse_zero_pad (N := N) source
      (q - source.length) ([] : List N.Sym))
  rw [hwrite]

private theorem copy_blank_transition {N : MultitapeTM}
    (coord dim out : Fin N.k) (a : Fin N.k → N.Sym)
    (hnonbit : a dim ≠ N.zero ∧ a dim ≠ N.one) :
    transition N coord dim out .copyDimensionBackward a =
      (.alignDimension, fun i => (a i,
        if i = dim ∨ i = out then .right else .stay)) := by
  apply Prod.ext
  · simp [transition, raw, hnonbit]
  · funext i
    by_cases hiD : i = dim
    · subst i
      simp [transition, raw, hnonbit, protect_self_move]
    · by_cases hiO : i = out
      · subst i
        simp [transition, raw, hnonbit, protect_self_move]
      · simp [transition, raw, hnonbit, hiD, hiO, protect_self_move]

/-- When the backward copy reaches the left marker, it enters alignment and
    moves both heads onto the first dimension bit and the first output bit. -/
theorem copy_dimension_end_step {N : MultitapeTM} (coord dim out : Fin N.k)
    (hc : coord ≠ N.inTape) (hd : dim ≠ N.inTape) (ho : out ≠ N.inTape)
    (hcd : coord ≠ dim) (hco : coord ≠ out) (hdo : dim ≠ out)
    (c : (control N coord dim out hc hd ho hcd hco hdo).machine.Cfg)
    (hs : c.state = State.copyDimensionBackward)
    (hnonbit : c.cells dim (c.head dim) ≠ N.zero ∧
      c.cells dim (c.head dim) ≠ N.one) :
    (machine N coord dim out hc hd ho hcd hco hdo).step c =
      ⟨State.alignDimension, c.cells,
        fun i => if i = dim ∨ i = out then c.head i + 1 else c.head i⟩ := by
  let P := control N coord dim out hc hd ho hcd hco hdo
  have ht := copy_blank_transition coord dim out
    (fun i => c.cells i (c.head i)) hnonbit
  apply cfg_ext P
  · change (transition N coord dim out c.state
      (fun i => c.cells i (c.head i))).1 = State.alignDimension
    rw [hs, ht]
  · funext i p
    change Function.update (c.cells i) (c.head i)
      (((transition N coord dim out c.state
        (fun j => c.cells j (c.head j))).2 i).1) p = c.cells i p
    rw [hs, ht]
    simp [Function.update_eq_self]
  · funext i
    change (match ((transition N coord dim out c.state
        (fun j => c.cells j (c.head j))).2 i).2 with
      | Move.left => c.head i - 1
      | Move.stay => c.head i
      | Move.right => c.head i + 1) = _
    rw [hs, ht]
    by_cases hiD : i = dim
    · subst i
      simp [hco]
    · by_cases hiO : i = out
      · subst i
        simp [Ne.symm hco]
      · simp [hiD, hiO]

private theorem align_bit_transition {N : MultitapeTM}
    (coord dim out : Fin N.k) (a : Fin N.k → N.Sym)
    (hbit : a dim = N.zero ∨ a dim = N.one) :
    transition N coord dim out .alignDimension a =
      (.alignDimension, fun i => (a i,
        if i = dim ∨ i = out then .right else .stay)) := by
  apply Prod.ext
  · simp [transition, raw, hbit]
  · funext i
    by_cases hiD : i = dim
    · subst i
      simp [transition, raw, hbit, protect_self_move]
    · by_cases hiO : i = out
      · subst i
        simp [transition, raw, hbit, protect_self_move]
      · simp [transition, raw, hbit, hiD, hiO, protect_self_move]

/-- On a dimension bit, alignment advances both the dimension and padded
    operand heads while preserving every tape cell. -/
theorem align_dimension_bit_step {N : MultitapeTM} (coord dim out : Fin N.k)
    (hc : coord ≠ N.inTape) (hd : dim ≠ N.inTape) (ho : out ≠ N.inTape)
    (hcd : coord ≠ dim) (hco : coord ≠ out) (hdo : dim ≠ out)
    (c : (control N coord dim out hc hd ho hcd hco hdo).machine.Cfg)
    (hs : c.state = State.alignDimension)
    (hbit : c.cells dim (c.head dim) = N.zero ∨
      c.cells dim (c.head dim) = N.one) :
    (machine N coord dim out hc hd ho hcd hco hdo).step c =
      ⟨State.alignDimension, c.cells,
        fun i => if i = dim ∨ i = out then c.head i + 1 else c.head i⟩ := by
  let P := control N coord dim out hc hd ho hcd hco hdo
  have ht := align_bit_transition coord dim out
    (fun i => c.cells i (c.head i)) hbit
  apply cfg_ext P
  · change (transition N coord dim out c.state
      (fun i => c.cells i (c.head i))).1 = State.alignDimension
    rw [hs, ht]
  · funext i p
    change Function.update (c.cells i) (c.head i)
      (((transition N coord dim out c.state
        (fun j => c.cells j (c.head j))).2 i).1) p = c.cells i p
    rw [hs, ht]
    simp [Function.update_eq_self]
  · funext i
    change (match ((transition N coord dim out c.state
        (fun j => c.cells j (c.head j))).2 i).2 with
      | Move.left => c.head i - 1
      | Move.stay => c.head i
      | Move.right => c.head i + 1) = _
    rw [hs, ht]
    by_cases hiD : i = dim
    · subst i
      simp [hco]
    · by_cases hiO : i = out
      · subst i
        simp [Ne.symm hco]
      · simp [hiD, hiO]

private def alignFrame {N : MultitapeTM} (coord dim out : Fin N.k)
    (hc : coord ≠ N.inTape) (hd : dim ≠ N.inTape) (ho : out ≠ N.inTape)
    (hcd : coord ≠ dim) (hco : coord ≠ out) (hdo : dim ≠ out)
    (base : (control N coord dim out hc hd ho hcd hco hdo).machine.Cfg)
    (dimension : List Bool) (outBits : List N.Sym)
    (dimensionHead outHead : ℕ) :
    (control N coord dim out hc hd ho hcd hco hdo).machine.Cfg where
  state := .alignDimension
  cells := fun i => if i = dim then N.tapeOf (dimension.map N.bitSym)
    else if i = out then N.tapeOf (N.blank :: outBits) else base.cells i
  head := fun i => if i = dim then dimensionHead
    else if i = out then outHead else base.head i

private theorem align_frame_bit_step {N : MultitapeTM} (coord dim out : Fin N.k)
    (hc : coord ≠ N.inTape) (hd : dim ≠ N.inTape) (ho : out ≠ N.inTape)
    (hcd : coord ≠ dim) (hco : coord ≠ out) (hdo : dim ≠ out)
    (base : (control N coord dim out hc hd ho hcd hco hdo).machine.Cfg)
    (pre rest : List Bool) (b : Bool) (outBits : List N.Sym)
    (outHead : ℕ) :
    (machine N coord dim out hc hd ho hcd hco hdo).step
      (alignFrame coord dim out hc hd ho hcd hco hdo base
        (pre ++ b :: rest) outBits (pre.length + 1) outHead) =
      alignFrame coord dim out hc hd ho hcd hco hdo base
        (pre ++ b :: rest) outBits (pre.length + 2) (outHead + 1) := by
  let P := control N coord dim out hc hd ho hcd hco hdo
  let c := alignFrame coord dim out hc hd ho hcd hco hdo base
    (pre ++ b :: rest) outBits (pre.length + 1) outHead
  have hscan : c.cells dim (c.head dim) = N.bitSym b := by
    simp [c, alignFrame, MultitapeTM.tapeOf, List.map_append, List.append_assoc]
  have hbit : c.cells dim (c.head dim) = N.zero ∨
      c.cells dim (c.head dim) = N.one := by
    rw [hscan]
    cases b <;> simp [MultitapeTM.bitSym]
  have hstep := align_dimension_bit_step coord dim out hc hd ho hcd hco hdo
    c rfl hbit
  rw [hstep]
  apply cfg_ext P
  · rfl
  · funext i p
    simp [c, alignFrame, hco, Ne.symm hco]
  · funext i
    by_cases hiD : i = dim
    · subst i
      simp [c, alignFrame, hco]
    · by_cases hiO : i = out
      · subst i
        simp [c, alignFrame, Ne.symm hco, Ne.symm hdo]
      · simp [c, alignFrame, hiD, hiO]

/-- Scanning the stored dimension repositions the caller-buffer head at the
    separator cell immediately after the padded first operand. -/
theorem align_dimension_run {N : MultitapeTM} (coord dim out : Fin N.k)
    (hc : coord ≠ N.inTape) (hd : dim ≠ N.inTape) (ho : out ≠ N.inTape)
    (hcd : coord ≠ dim) (hco : coord ≠ out) (hdo : dim ≠ out)
    (base : (control N coord dim out hc hd ho hcd hco hdo).machine.Cfg)
    (pre rest : List Bool) (outBits : List N.Sym) (outHead : ℕ) :
    (machine N coord dim out hc hd ho hcd hco hdo).step^[rest.length]
      (alignFrame coord dim out hc hd ho hcd hco hdo base
        (pre ++ rest) outBits (pre.length + 1) outHead) =
      alignFrame coord dim out hc hd ho hcd hco hdo base
        (pre ++ rest) outBits (pre.length + rest.length + 1)
        (outHead + rest.length) := by
  induction rest generalizing pre outHead with
  | nil => simp [alignFrame]
  | cons b rest ih =>
      rw [List.length_cons, Function.iterate_succ_apply, align_frame_bit_step]
      have htail := ih (pre ++ [b]) (outHead + 1)
      simpa [List.length_append, List.append_assoc, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using htail

/-- The staged dimension buffer, after reverse copy and the marker exit, is
    aligned with the dimension head at its first bit and the output head at
    the first copied bit. -/
theorem copy_then_align_start {N : MultitapeTM} (coord dim out : Fin N.k)
    (hc : coord ≠ N.inTape) (hd : dim ≠ N.inTape) (ho : out ≠ N.inTape)
    (hcd : coord ≠ dim) (hco : coord ≠ out) (hdo : dim ≠ out)
    (base : (control N coord dim out hc hd ho hcd hco hdo).machine.Cfg)
    (source : List Bool) (q : ℕ)
    (hsource : base.cells dim = N.tapeOf (source.map N.bitSym))
    (hout : ∀ p, 1 ≤ p → (N.tapeOf (N.blank :: List.replicate q N.zero)) p ≠ N.startSym)
    (hq : source.length ≤ q) :
    (machine N coord dim out hc hd ho hcd hco hdo).step^[source.length + 1]
      (copyFrame coord dim out hc hd ho hcd hco hdo base source
        (N.tapeOf (N.blank :: List.replicate q N.zero)) (q + 1)) =
      alignFrame coord dim out hc hd ho hcd hco hdo base source
        (List.replicate (q - source.length) N.zero ++ source.map N.bitSym)
        1 (q - source.length + 2) := by
  have hcopy := copy_dimension_zero_padded coord dim out hc hd ho hcd hco hdo
    base source q hsource hout hq
  have hmarker : base.cells dim 0 = N.startSym := by
    rw [hsource]
    simp [MultitapeTM.tapeOf]
  have hnonbit :
      (copyFrame coord dim out hc hd ho hcd hco hdo base []
        (N.tapeOf (N.blank :: List.replicate (q - source.length) N.zero ++
          source.map N.bitSym)) (q + 1 - source.length)).cells dim
        ((copyFrame coord dim out hc hd ho hcd hco hdo base []
          (N.tapeOf (N.blank :: List.replicate (q - source.length) N.zero ++
            source.map N.bitSym)) (q + 1 - source.length)).head dim) ≠ N.zero ∧
      (copyFrame coord dim out hc hd ho hcd hco hdo base []
        (N.tapeOf (N.blank :: List.replicate (q - source.length) N.zero ++
          source.map N.bitSym)) (q + 1 - source.length)).cells dim
        ((copyFrame coord dim out hc hd ho hcd hco hdo base []
          (N.tapeOf (N.blank :: List.replicate (q - source.length) N.zero ++
            source.map N.bitSym)) (q + 1 - source.length)).head dim) ≠ N.one := by
    rw [show (copyFrame coord dim out hc hd ho hcd hco hdo base []
        (N.tapeOf (N.blank :: List.replicate (q - source.length) N.zero ++
          source.map N.bitSym)) (q + 1 - source.length)).head dim = 0 by simp [copyFrame]]
    rw [show (copyFrame coord dim out hc hd ho hcd hco hdo base []
        (N.tapeOf (N.blank :: List.replicate (q - source.length) N.zero ++
          source.map N.bitSym)) (q + 1 - source.length)).cells dim = base.cells dim by
      simp [copyFrame, hdo, Ne.symm hdo]]
    rw [hmarker]
    exact ⟨start_ne_zero, start_ne_one⟩
  have hend := copy_dimension_end_step coord dim out hc hd ho hcd hco hdo
    (copyFrame coord dim out hc hd ho hcd hco hdo base []
      (N.tapeOf (N.blank :: List.replicate (q - source.length) N.zero ++
        source.map N.bitSym)) (q + 1 - source.length)) rfl hnonbit
  have hframe : (machine N coord dim out hc hd ho hcd hco hdo).step
      (copyFrame coord dim out hc hd ho hcd hco hdo base []
        (N.tapeOf (N.blank :: List.replicate (q - source.length) N.zero ++
          source.map N.bitSym)) (q + 1 - source.length)) =
      alignFrame coord dim out hc hd ho hcd hco hdo base source
        (List.replicate (q - source.length) N.zero ++ source.map N.bitSym)
        1 (q - source.length + 2) := by
    rw [hend]
    apply cfg_ext (control N coord dim out hc hd ho hcd hco hdo)
    · rfl
    · funext i p
      by_cases hiO : i = out
      · subst i
        simp [copyFrame, alignFrame, hdo, Ne.symm hdo]
      · by_cases hiD : i = dim
        · subst i
          simp [copyFrame, alignFrame, hsource, hdo, Ne.symm hdo]
        · simp [copyFrame, alignFrame, hiO, hiD]
    · funext i
      by_cases hiD : i = dim
      · subst i
        simp [copyFrame, alignFrame, hdo, Ne.symm hdo]
      · by_cases hiO : i = out
        · subst i
          simp [copyFrame, alignFrame, hdo, Ne.symm hdo]
          omega
        · simp [copyFrame, alignFrame, hiD, hiO]
  rw [Function.iterate_succ_apply', hcopy, hframe]

private theorem align_blank_transition {N : MultitapeTM}
    (coord dim out : Fin N.k) (a : Fin N.k → N.Sym)
    (hnonbit : a dim ≠ N.zero ∧ a dim ≠ N.one) :
    transition N coord dim out .alignDimension a =
      (.writeSeparator, fun i => (a i, .stay)) := by
  apply Prod.ext
  · simp [transition, raw, hnonbit]
  · funext i
    simp [transition, raw, hnonbit, protect_self_move]

/-- At the blank after the dimension, leave the aligned heads in place and
    enter the separator-writing state. -/
theorem align_dimension_end_step {N : MultitapeTM} (coord dim out : Fin N.k)
    (hc : coord ≠ N.inTape) (hd : dim ≠ N.inTape) (ho : out ≠ N.inTape)
    (hcd : coord ≠ dim) (hco : coord ≠ out) (hdo : dim ≠ out)
    (c : (control N coord dim out hc hd ho hcd hco hdo).machine.Cfg)
    (hs : c.state = State.alignDimension)
    (hnonbit : c.cells dim (c.head dim) ≠ N.zero ∧
      c.cells dim (c.head dim) ≠ N.one) :
    (machine N coord dim out hc hd ho hcd hco hdo).step c =
      ⟨State.writeSeparator, c.cells, c.head⟩ := by
  let P := control N coord dim out hc hd ho hcd hco hdo
  have ht := align_blank_transition coord dim out
    (fun i => c.cells i (c.head i)) hnonbit
  apply cfg_ext P
  · change (transition N coord dim out c.state
      (fun i => c.cells i (c.head i))).1 = State.writeSeparator
    rw [hs, ht]
  · funext i p
    change Function.update (c.cells i) (c.head i)
      (((transition N coord dim out c.state
        (fun j => c.cells j (c.head j))).2 i).1) p = c.cells i p
    rw [hs, ht]
    simp [Function.update_eq_self]
  · funext i
    change (match ((transition N coord dim out c.state
        (fun j => c.cells j (c.head j))).2 i).2 with
      | Move.left => c.head i - 1
      | Move.stay => c.head i
      | Move.right => c.head i + 1) = c.head i
    rw [hs, ht]

private theorem write_separator_transition {N : MultitapeTM}
    (coord dim out : Fin N.k) (a : Fin N.k → N.Sym)
    (hout : a out ≠ N.startSym) :
    transition N coord dim out .writeSeparator a =
      (.rewindCoordinate, fun i =>
        (if i = out then N.sep else a i,
          if i = out then .right else .stay)) := by
  apply Prod.ext
  · simp [transition, raw]
  · funext i
    by_cases hi : i = out
    · subst i
      simp [transition, raw, protect, hout, sep_ne_start]
    · simp [transition, raw, hi, protect_self_move]

/-- Write the separator immediately after the staged q-bit dimension operand. -/
theorem write_separator_step {N : MultitapeTM} (coord dim out : Fin N.k)
    (hc : coord ≠ N.inTape) (hd : dim ≠ N.inTape) (ho : out ≠ N.inTape)
    (hcd : coord ≠ dim) (hco : coord ≠ out) (hdo : dim ≠ out)
    (c : (control N coord dim out hc hd ho hcd hco hdo).machine.Cfg)
    (hs : c.state = State.writeSeparator)
    (hout : c.cells out (c.head out) ≠ N.startSym) :
    (machine N coord dim out hc hd ho hcd hco hdo).step c =
      ⟨State.rewindCoordinate,
        fun i => if i = out then Function.update (c.cells i) (c.head i) N.sep
          else c.cells i,
        fun i => if i = out then c.head i + 1 else c.head i⟩ := by
  let P := control N coord dim out hc hd ho hcd hco hdo
  have ht := write_separator_transition coord dim out
    (fun i => c.cells i (c.head i)) hout
  apply cfg_ext P
  · change (transition N coord dim out c.state
      (fun i => c.cells i (c.head i))).1 = State.rewindCoordinate
    rw [hs, ht]
  · funext i p
    change Function.update (c.cells i) (c.head i)
      (((transition N coord dim out c.state
        (fun j => c.cells j (c.head j))).2 i).1) p = _
    rw [hs, ht]
    by_cases hi : i = out
    · subst i
      simp
    · simp [hi]
  · funext i
    change (match ((transition N coord dim out c.state
        (fun j => c.cells j (c.head j))).2 i).2 with
      | Move.left => c.head i - 1
      | Move.stay => c.head i
      | Move.right => c.head i + 1) = _
    rw [hs, ht]
    by_cases hi : i = out <;> simp [hi]

private def separatorFrame {N : MultitapeTM} (coord dim out : Fin N.k)
    (hc : coord ≠ N.inTape) (hd : dim ≠ N.inTape) (ho : out ≠ N.inTape)
    (hcd : coord ≠ dim) (hco : coord ≠ out) (hdo : dim ≠ out)
    (base : (control N coord dim out hc hd ho hcd hco hdo).machine.Cfg)
    (dimension : List Bool) (outBits : List N.Sym) (outHead : ℕ) :
    (control N coord dim out hc hd ho hcd hco hdo).machine.Cfg where
  state := .rewindCoordinate
  cells := fun i => if i = dim then N.tapeOf (dimension.map N.bitSym)
    else if i = out then N.tapeOf (N.blank :: outBits ++ [N.sep]) else base.cells i
  head := fun i => if i = dim then dimension.length + 1
    else if i = out then outHead + dimension.length + 1 else base.head i

/-- Once aligned at the first separator cell, two transitions leave the
    controller in coordinate-rewind state with `operand₁ ++ sep` on its buffer. -/
theorem align_to_separator_run {N : MultitapeTM} (coord dim out : Fin N.k)
    (hc : coord ≠ N.inTape) (hd : dim ≠ N.inTape) (ho : out ≠ N.inTape)
    (hcd : coord ≠ dim) (hco : coord ≠ out) (hdo : dim ≠ out)
    (base : (control N coord dim out hc hd ho hcd hco hdo).machine.Cfg)
    (dimension : List Bool) (outBits : List N.Sym) (outHead : ℕ)
    (hdim : (N.tapeOf (dimension.map N.bitSym)) (dimension.length + 1) = N.blank)
    (hout : (N.tapeOf (N.blank :: outBits)) (outHead + dimension.length) = N.blank)
    (hpos : outHead + dimension.length = outBits.length + 2) :
    (machine N coord dim out hc hd ho hcd hco hdo).step^[dimension.length + 2]
      (alignFrame coord dim out hc hd ho hcd hco hdo base
        dimension outBits 1 outHead) =
      separatorFrame coord dim out hc hd ho hcd hco hdo base
        dimension outBits outHead := by
  have hrun := align_dimension_run coord dim out hc hd ho hcd hco hdo
    base [] dimension outBits outHead
  have hrun' : (machine N coord dim out hc hd ho hcd hco hdo).step^[dimension.length]
      (alignFrame coord dim out hc hd ho hcd hco hdo base dimension outBits 1 outHead) =
      alignFrame coord dim out hc hd ho hcd hco hdo base dimension outBits
        (dimension.length + 1) (outHead + dimension.length) := by
    simpa using hrun
  have hnonbit :
      (alignFrame coord dim out hc hd ho hcd hco hdo base dimension outBits
        (dimension.length + 1) (outHead + dimension.length)).cells dim
        ((alignFrame coord dim out hc hd ho hcd hco hdo base dimension outBits
          (dimension.length + 1) (outHead + dimension.length)).head dim) ≠ N.zero ∧
      (alignFrame coord dim out hc hd ho hcd hco hdo base dimension outBits
        (dimension.length + 1) (outHead + dimension.length)).cells dim
        ((alignFrame coord dim out hc hd ho hcd hco hdo base dimension outBits
          (dimension.length + 1) (outHead + dimension.length)).head dim) ≠ N.one := by
    rw [show (alignFrame coord dim out hc hd ho hcd hco hdo base dimension outBits
        (dimension.length + 1) (outHead + dimension.length)).head dim =
          dimension.length + 1 by simp [alignFrame]]
    rw [show (alignFrame coord dim out hc hd ho hcd hco hdo base dimension outBits
        (dimension.length + 1) (outHead + dimension.length)).cells dim =
          N.tapeOf (dimension.map N.bitSym) by simp [alignFrame, hdo, Ne.symm hdo]]
    rw [hdim]
    exact ⟨blank_ne_zero, blank_ne_one⟩
  have hend := align_dimension_end_step coord dim out hc hd ho hcd hco hdo
    (alignFrame coord dim out hc hd ho hcd hco hdo base dimension outBits
      (dimension.length + 1) (outHead + dimension.length)) rfl hnonbit
  have hcell :
      (alignFrame coord dim out hc hd ho hcd hco hdo base dimension outBits
        (dimension.length + 1) (outHead + dimension.length)).cells out
        ((alignFrame coord dim out hc hd ho hcd hco hdo base dimension outBits
          (dimension.length + 1) (outHead + dimension.length)).head out) = N.blank := by
    simpa [alignFrame, hdo, Ne.symm hdo] using hout
  have hstate : ((machine N coord dim out hc hd ho hcd hco hdo).step
      (alignFrame coord dim out hc hd ho hcd hco hdo base dimension outBits
        (dimension.length + 1) (outHead + dimension.length))).state = State.writeSeparator := by
    rw [hend]
  have hcellStep : ((machine N coord dim out hc hd ho hcd hco hdo).step
      (alignFrame coord dim out hc hd ho hcd hco hdo base dimension outBits
        (dimension.length + 1) (outHead + dimension.length))).cells out
      (((machine N coord dim out hc hd ho hcd hco hdo).step
        (alignFrame coord dim out hc hd ho hcd hco hdo base dimension outBits
          (dimension.length + 1) (outHead + dimension.length))).head out) = N.blank := by
    rw [hend]
    exact hcell
  have hwrite := write_separator_step coord dim out hc hd ho hcd hco hdo
    ((machine N coord dim out hc hd ho hcd hco hdo).step
      (alignFrame coord dim out hc hd ho hcd hco hdo base dimension outBits
        (dimension.length + 1) (outHead + dimension.length)))
    hstate (by rw [hcellStep]; exact blank_ne_start)
  rw [hend] at hwrite
  have hiter : (machine N coord dim out hc hd ho hcd hco hdo).step^[dimension.length + 2]
      (alignFrame coord dim out hc hd ho hcd hco hdo base
        dimension outBits 1 outHead) =
      (machine N coord dim out hc hd ho hcd hco hdo).step
        ((machine N coord dim out hc hd ho hcd hco hdo).step
          ((machine N coord dim out hc hd ho hcd hco hdo).step^[dimension.length]
          (alignFrame coord dim out hc hd ho hcd hco hdo base
            dimension outBits 1 outHead))) := by
    rw [show dimension.length + 2 = (dimension.length + 1) + 1 by omega,
      Function.iterate_succ_apply', Function.iterate_succ_apply']
  rw [hiter, hrun', hend, hwrite]
  apply cfg_ext (control N coord dim out hc hd ho hcd hco hdo)
  · rfl
  · funext i p
    by_cases hiD : i = dim
    · subst i
      simp [separatorFrame, alignFrame, hdo]
    · by_cases hiO : i = out
      · subst i
        simp [separatorFrame, alignFrame, hiD, hco, hdo]
        have hidx : outHead + dimension.length =
            (N.blank :: outBits).length + 1 := by simp; omega
        have happ := tape_append N (N.blank :: outBits) N.sep
        rw [← hidx] at happ
        exact congrArg (fun f => f p) happ
      · simp [separatorFrame, alignFrame, hiD, hiO]
  · funext i
    by_cases hiD : i = dim
    · subst i
      simp [separatorFrame, alignFrame, hdo, Ne.symm hdo]
    · by_cases hiO : i = out
      · subst i
        simp [separatorFrame, alignFrame, Ne.symm hco, Ne.symm hdo]
      · simp [separatorFrame, alignFrame, hiD, hiO]

/-- From the padded first-operand frame at the dimension terminator, back up
    both heads, copy the stored dimension over the zero prefix, align the scan,
    and write the separator. -/
theorem dimension_copy_separator_run {N : MultitapeTM}
    (coord dim out : Fin N.k)
    (hc : coord ≠ N.inTape) (hd : dim ≠ N.inTape) (ho : out ≠ N.inTape)
    (hcd : coord ≠ dim) (hco : coord ≠ out) (hdo : dim ≠ out)
    (base : (control N coord dim out hc hd ho hcd hco hdo).machine.Cfg)
    (dimension record : List Bool) (q : ℕ)
    (hdimCells : base.cells dim = N.tapeOf (dimension.map N.bitSym))
    (hdimHead : base.head dim = dimension.length + 1)
    (hcoordCells : base.cells coord = N.tapeOf (record.map N.bitSym))
    (hcoordHead : base.head coord = q + 3)
    (hq : dimension.length ≤ q)
    (hpad : ∀ p, 1 ≤ p →
      (N.tapeOf (N.blank :: List.replicate q N.zero)) p ≠ N.startSym)
    (hdimBlank : (N.tapeOf (dimension.map N.bitSym)) (dimension.length + 1) = N.blank) :
    (machine N coord dim out hc hd ho hcd hco hdo).step^[2 * dimension.length + 4]
      (seekAfterFillFrame coord dim out hc hd ho hcd hco hdo base record
        (List.replicate q N.zero) (q + 3)) =
      separatorFrame coord dim out hc hd ho hcd hco hdo base dimension
        (List.replicate (q - dimension.length) N.zero ++ dimension.map N.bitSym)
        (q - dimension.length + 2) := by
  let padded := List.replicate (q - dimension.length) N.zero ++ dimension.map N.bitSym
  let paddedCells := N.tapeOf (N.blank :: List.replicate q N.zero)
  let outHead := q - dimension.length + 2
  let start := seekAfterFillFrame coord dim out hc hd ho hcd hco hdo base record
    (List.replicate q N.zero) (q + 3)
  have hnonbit : start.cells dim (start.head dim) ≠ N.zero ∧
      start.cells dim (start.head dim) ≠ N.one := by
    rw [show start.cells dim (start.head dim) = N.blank by
      simp [start, seekAfterFillFrame, hdimCells, hdimHead, hcd, Ne.symm hcd, hdo, Ne.symm hdo, hdimBlank]]
    exact ⟨blank_ne_zero, blank_ne_one⟩
  have hdim : start.cells dim (start.head dim) ≠ N.startSym := by
    rw [show start.cells dim (start.head dim) = N.blank by
      simp [start, seekAfterFillFrame, hdimCells, hdimHead, hcd, Ne.symm hcd, hdo, Ne.symm hdo, hdimBlank]]
    exact blank_ne_start
  have hout : start.cells out (start.head out) ≠ N.startSym := by
    have hc : start.cells out (start.head out) =
        (N.tapeOf (N.blank :: List.replicate q N.zero)) (q + 2) := by
      simp [start, seekAfterFillFrame, hco, Ne.symm hco, hdo, Ne.symm hdo]
    rw [hc]
    exact hpad (q + 2) (by omega)
  have hhd : 1 ≤ start.head dim := by
    simp [start, seekAfterFillFrame, hdimHead, Ne.symm hcd, hdo, Ne.symm hdo]
  have hho : 1 ≤ start.head out := by
    simp [start, seekAfterFillFrame, Ne.symm hco, hdo, Ne.symm hdo]
  have hend := seek_dimension_end_step coord dim out hc hd ho hcd hco hdo
    start rfl hnonbit hdim hout hhd hho
  have hcopyStart : (machine N coord dim out hc hd ho hcd hco hdo).step start =
      copyFrame coord dim out hc hd ho hcd hco hdo base dimension paddedCells (q + 1) := by
    rw [hend]
    apply cfg_ext (control N coord dim out hc hd ho hcd hco hdo)
    · rfl
    · funext i p
      by_cases hiD : i = dim
      · subst i
        simp [start, seekAfterFillFrame, copyFrame, hdimCells, hcd, Ne.symm hcd, hdo, Ne.symm hdo]
      · by_cases hiO : i = out
        · subst i
          simp [start, seekAfterFillFrame, copyFrame, MultitapeTM.tapeOf, paddedCells,
            hco, Ne.symm hco, hdo, Ne.symm hdo, List.length_replicate]
        · by_cases hiC : i = coord
          · subst i
            simp [start, seekAfterFillFrame, copyFrame, hcoordCells, hco, Ne.symm hco, hcd, Ne.symm hcd]
          · simp [start, seekAfterFillFrame, copyFrame, hiD, hiO, hiC, hcd, hco, hdo, Ne.symm hcd, Ne.symm hco, Ne.symm hdo]
    · funext i
      by_cases hiD : i = dim
      · subst i
        simp [start, seekAfterFillFrame, copyFrame, hdimHead, Ne.symm hcd, hdo, Ne.symm hdo]
      · by_cases hiO : i = out
        · subst i
          simp [start, seekAfterFillFrame, copyFrame, Ne.symm hco, hdo, Ne.symm hdo]
        · by_cases hiC : i = coord
          · subst i
            simp [start, seekAfterFillFrame, copyFrame, hcoordHead, hiD, hiO]
          · simp [start, seekAfterFillFrame, copyFrame, hiD, hiO, hiC, hcd, hco, hdo, Ne.symm hcd, Ne.symm hco, Ne.symm hdo]
  have hcopy := copy_then_align_start coord dim out hc hd ho hcd hco hdo
    base dimension q hdimCells hpad hq
  have hpos : outHead + dimension.length = padded.length + 2 := by
    simp [outHead, padded, List.length_append, List.length_replicate,
      List.length_map]
    omega
  have houtBlank : (N.tapeOf (N.blank :: padded))
      (outHead + dimension.length) = N.blank := by
    rw [hpos]
    simp [MultitapeTM.tapeOf, padded, List.length_append,
      List.length_replicate, List.length_map]
  have hseparator := align_to_separator_run coord dim out hc hd ho hcd hco hdo
    base dimension padded outHead hdimBlank houtBlank hpos
  have hstage :
      (machine N coord dim out hc hd ho hcd hco hdo).step^[dimension.length + 2] start =
        alignFrame coord dim out hc hd ho hcd hco hdo base dimension padded
          1 outHead := by
    rw [show dimension.length + 2 = (dimension.length + 1) + 1 by omega,
      Function.iterate_add_apply]
    simp only [Function.iterate_one]
    rw [hcopyStart]
    simpa [padded, paddedCells, outHead] using hcopy
  rw [show 2 * dimension.length + 4 =
      (dimension.length + 2) + (dimension.length + 2) by omega,
    Function.iterate_add_apply, hstage, hseparator]

/-- Exact first-operand staging: the signed record supplies the q-step
    padding clock, then the retained dimension is copied into the final slots
    and the separator is written. -/
theorem first_operand_separator_run {N : MultitapeTM}
    (coord dim out : Fin N.k)
    (hc : coord ≠ N.inTape) (hd : dim ≠ N.inTape) (ho : out ≠ N.inTape)
    (hcd : coord ≠ dim) (hco : coord ≠ out) (hdo : dim ≠ out)
    (base : (control N coord dim out hc hd ho hcd hco hdo).machine.Cfg)
    (dimension low : List Bool) (sign high : Bool)
    (hdimCells : base.cells dim = N.tapeOf (dimension.map N.bitSym))
    (hdimHead : base.head dim = dimension.length + 1)
    (hcoordCells : base.cells coord =
      N.tapeOf (([sign, high] ++ low).map N.bitSym))
    (hcoordHead : base.head coord = low.length + 3)
    (hq : dimension.length ≤ low.length)
    (hpad : ∀ p, 1 ≤ p →
      (N.tapeOf (N.blank :: List.replicate low.length N.zero)) p ≠ N.startSym)
    (hdimBlank : (N.tapeOf (dimension.map N.bitSym))
      (dimension.length + 1) = N.blank) :
    (machine N coord dim out hc hd ho hcd hco hdo).step^[
      2 * dimension.length + low.length + 7]
      (initialStageFrame coord dim out hc hd ho hcd hco hdo base
        ([sign, high] ++ low)) =
      separatorFrame coord dim out hc hd ho hcd hco hdo base dimension
        (List.replicate (low.length - dimension.length) N.zero ++
          dimension.map N.bitSym)
        (low.length - dimension.length + 2) := by
  have hfill := signed_fill_seek_run coord dim out hc hd ho hcd hco hdo
    base sign high low
  have hcopy := dimension_copy_separator_run coord dim out hc hd ho hcd hco hdo
    base dimension ([sign, high] ++ low) low.length hdimCells hdimHead
    hcoordCells hcoordHead hq hpad hdimBlank
  rw [show 2 * dimension.length + low.length + 7 =
      (2 * dimension.length + 4) + (low.length + 3) by omega,
    Function.iterate_add_apply, hfill]
  exact hcopy

private theorem copy_coordinate_transition {N : MultitapeTM}
    (coord dim out : Fin N.k) (a : Fin N.k → N.Sym)
    (hbit : a coord = N.zero ∨ a coord = N.one)
    (hcoord : a coord ≠ N.startSym) (hout : a out ≠ N.startSym)
    (hco : coord ≠ out) :
    transition N coord dim out .copyCoordinate a =
      (.copyCoordinate, fun i =>
        (if i = out then a coord else a i,
          if i = coord ∨ i = out then .right else .stay)) := by
  rcases hbit with hz | hone
  · have hr : raw N coord dim out .copyCoordinate a =
        (.copyCoordinate, fun i =>
          (if i = out then a coord else a i,
            if i = coord ∨ i = out then .right else .stay)) := by
      simp [raw, hz]
    unfold transition
    simp only [hr]
    apply Prod.ext
    · rfl
    · funext i
      by_cases hiO : i = out
      · subst i
        simp [protect, hout, hcoord, Ne.symm hco]
      · by_cases hiC : i = coord
        · subst i
          simp [protect, hcoord, hiO, Ne.symm hco]
        · by_cases h : a i = N.startSym <;> simp [protect, hiO, hiC, h]
  · have hr : raw N coord dim out .copyCoordinate a =
        (.copyCoordinate, fun i =>
          (if i = out then a coord else a i,
            if i = coord ∨ i = out then .right else .stay)) := by
      simp [raw, hone]
    unfold transition
    simp only [hr]
    apply Prod.ext
    · rfl
    · funext i
      by_cases hiO : i = out
      · subst i
        simp [protect, hout, hcoord, Ne.symm hco]
      · by_cases hiC : i = coord
        · subst i
          simp [protect, hcoord, hiO, Ne.symm hco]
        · by_cases h : a i = N.startSym <;> simp [protect, hiO, hiC, h]

private theorem copy_coordinate_bit_step {N : MultitapeTM}
    (coord dim out : Fin N.k)
    (hc : coord ≠ N.inTape) (hd : dim ≠ N.inTape) (ho : out ≠ N.inTape)
    (hcd : coord ≠ dim) (hco : coord ≠ out) (hdo : dim ≠ out)
    (c : (control N coord dim out hc hd ho hcd hco hdo).machine.Cfg)
    (hs : c.state = State.copyCoordinate)
    (hbit : c.cells coord (c.head coord) = N.zero ∨
      c.cells coord (c.head coord) = N.one)
    (hout : c.cells out (c.head out) ≠ N.startSym) :
    (machine N coord dim out hc hd ho hcd hco hdo).step c =
      ⟨State.copyCoordinate,
        fun i => if i = out then Function.update (c.cells i) (c.head i)
          (c.cells coord (c.head coord)) else c.cells i,
        fun i => if i = coord ∨ i = out then c.head i + 1 else c.head i⟩ := by
  have hcoord : c.cells coord (c.head coord) ≠ N.startSym := by
    rcases hbit with hz | hz
    · rw [hz]
      have hn := N.syms_distinct
      simp only [List.nodup_cons, List.mem_cons, not_or] at hn
      exact Ne.symm hn.2.1.1
    · rw [hz]
      have hn := N.syms_distinct
      simp only [List.nodup_cons, List.mem_cons, not_or] at hn
      exact Ne.symm hn.2.1.2.1
  have ht := copy_coordinate_transition coord dim out
    (fun i => c.cells i (c.head i)) hbit hcoord hout hco
  apply cfg_ext (control N coord dim out hc hd ho hcd hco hdo)
  · change (transition N coord dim out c.state
      (fun i => c.cells i (c.head i))).1 = State.copyCoordinate
    rw [hs, ht]
  · funext i p
    change Function.update (c.cells i) (c.head i)
      (((transition N coord dim out c.state
        (fun j => c.cells j (c.head j))).2 i).1) p = _
    rw [hs, ht]
    by_cases hi : i = out
    · subst i
      simp
    · simp [hi]
  · funext i
    change (match ((transition N coord dim out c.state
        (fun j => c.cells j (c.head j))).2 i).2 with
      | Move.left => c.head i - 1
      | Move.stay => c.head i
      | Move.right => c.head i + 1) = _
    rw [hs, ht]
    by_cases hiC : i = coord
    · subst i
      simp [hco]
    · by_cases hiO : i = out
      · subst i
        simp [Ne.symm hco]
      · simp [hiC, hiO]

/-- Copy a designated coordinate suffix into the caller buffer, preserving
    the sign/high-bit prefix and all other tapes. -/
theorem copy_coordinate_suffix_run {N : MultitapeTM}
    (coord dim out : Fin N.k)
    (hc : coord ≠ N.inTape) (hd : dim ≠ N.inTape) (ho : out ≠ N.inTape)
    (hcd : coord ≠ dim) (hco : coord ≠ out) (hdo : dim ≠ out)
    (base : (control N coord dim out hc hd ho hcd hco hdo).machine.Cfg)
    (pre rest : List Bool) (outBits : List N.Sym) :
    (machine N coord dim out hc hd ho hcd hco hdo).step^[rest.length]
      (BankedOperandStageProofSupport.coordinateCopyFrame coord dim out hc hd ho hcd hco hdo base
        (pre ++ rest) outBits (pre.length + 1) (outBits.length + 2)) =
      coordinateCopyFrame coord dim out hc hd ho hcd hco hdo base
        (pre ++ rest) (outBits ++ rest.map N.bitSym)
        (pre.length + rest.length + 1) (outBits.length + rest.length + 2) := by
  induction rest generalizing pre outBits with
  | nil => simp [coordinateCopyFrame]
  | cons b rest ih =>
      let c := coordinateCopyFrame coord dim out hc hd ho hcd hco hdo base
        (pre ++ b :: rest) outBits (pre.length + 1) (outBits.length + 2)
      have hscan : c.cells coord (c.head coord) = N.bitSym b := by
        simp [c, coordinateCopyFrame, MultitapeTM.tapeOf,
          List.map_append, List.append_assoc]
      have hbit : c.cells coord (c.head coord) = N.zero ∨
          c.cells coord (c.head coord) = N.one := by
        rw [hscan]
        cases b <;> simp [MultitapeTM.bitSym]
      have hout : c.cells out (c.head out) ≠ N.startSym := by
        have hb : c.cells out (c.head out) = N.blank := by
          simp [c, coordinateCopyFrame, MultitapeTM.tapeOf, Ne.symm hco]
        rw [hb]
        have hn := N.syms_distinct
        simp only [List.nodup_cons, List.mem_cons, not_or] at hn
        exact hn.1.1
      have hstep := copy_coordinate_bit_step coord dim out hc hd ho hcd hco hdo
        c rfl hbit hout
      have happ : Function.update (N.tapeOf (N.blank :: outBits))
          (outBits.length + 2) (N.bitSym b) =
          N.tapeOf (N.blank :: outBits ++ [N.bitSym b]) := by
        have ht := tape_append N (N.blank :: outBits) (N.bitSym b)
        simpa [List.length_cons, Nat.add_assoc] using ht
      have hframe : (machine N coord dim out hc hd ho hcd hco hdo).step c =
          coordinateCopyFrame coord dim out hc hd ho hcd hco hdo base
            (pre ++ b :: rest) (outBits ++ [N.bitSym b])
            (pre.length + 2) (outBits.length + 3) := by
        rw [hstep]
        apply cfg_ext (control N coord dim out hc hd ho hcd hco hdo)
        · rfl
        · funext i p
          by_cases hi : i = out
          · subst i
            rw [hscan]
            simp [c, coordinateCopyFrame, hco, Ne.symm hco, happ]
          · simp [c, coordinateCopyFrame, hi, hco]
        · funext i
          by_cases hiC : i = coord
          · subst i
            simp [c, coordinateCopyFrame, hco, Ne.symm hco]
          · by_cases hiO : i = out
            · subst i
              simp [c, coordinateCopyFrame, Ne.symm hco]
            · simp [c, coordinateCopyFrame, hiC, hiO]
      rw [List.length_cons, Function.iterate_succ_apply, hframe]
      have htail := ih (pre ++ [b]) (outBits ++ [N.bitSym b])
      simpa [coordinateCopyFrame, List.map_append, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail

private theorem copy_coordinate_blank_transition {N : MultitapeTM}
    (coord dim out : Fin N.k) (a : Fin N.k → N.Sym)
    (hnonbit : a coord ≠ N.zero ∧ a coord ≠ N.one) :
    transition N coord dim out .copyCoordinate a =
      (.halt, fun i => (a i, .stay)) := by
  apply Prod.ext
  · simp [transition, raw, hnonbit]
  · funext i
    simp [transition, raw, hnonbit, protect_self_move]

private theorem copy_coordinate_end_step {N : MultitapeTM}
    (coord dim out : Fin N.k)
    (hc : coord ≠ N.inTape) (hd : dim ≠ N.inTape) (ho : out ≠ N.inTape)
    (hcd : coord ≠ dim) (hco : coord ≠ out) (hdo : dim ≠ out)
    (c : (control N coord dim out hc hd ho hcd hco hdo).machine.Cfg)
    (hs : c.state = State.copyCoordinate)
    (hnonbit : c.cells coord (c.head coord) ≠ N.zero ∧
      c.cells coord (c.head coord) ≠ N.one) :
    (machine N coord dim out hc hd ho hcd hco hdo).step c =
      ⟨State.halt, c.cells, c.head⟩ := by
  have ht := copy_coordinate_blank_transition coord dim out
    (fun i => c.cells i (c.head i)) hnonbit
  apply cfg_ext (control N coord dim out hc hd ho hcd hco hdo)
  · change (transition N coord dim out c.state
      (fun i => c.cells i (c.head i))).1 = State.halt
    rw [hs, ht]
  · funext i p
    change Function.update (c.cells i) (c.head i)
      (((transition N coord dim out c.state
        (fun j => c.cells j (c.head j))).2 i).1) p = c.cells i p
    rw [hs, ht]
    simp
  · funext i
    change (match ((transition N coord dim out c.state
        (fun j => c.cells j (c.head j))).2 i).2 with
      | Move.left => c.head i - 1
      | Move.stay => c.head i
      | Move.right => c.head i + 1) = c.head i
    rw [hs, ht]

/-- The coordinate copy stops at the first blank, leaving a halted caller
    frame with exactly the copied suffix appended. -/
theorem copy_coordinate_suffix_to_halt {N : MultitapeTM}
    (coord dim out : Fin N.k)
    (hc : coord ≠ N.inTape) (hd : dim ≠ N.inTape) (ho : out ≠ N.inTape)
    (hcd : coord ≠ dim) (hco : coord ≠ out) (hdo : dim ≠ out)
    (base : (control N coord dim out hc hd ho hcd hco hdo).machine.Cfg)
    (pre rest : List Bool) (outBits : List N.Sym) :
    (machine N coord dim out hc hd ho hcd hco hdo).step^[rest.length + 1]
      (coordinateCopyFrame coord dim out hc hd ho hcd hco hdo base
        (pre ++ rest) outBits (pre.length + 1) (outBits.length + 2)) =
      ⟨State.halt,
        (coordinateCopyFrame coord dim out hc hd ho hcd hco hdo base
          (pre ++ rest) (outBits ++ rest.map N.bitSym)
          (pre.length + rest.length + 1) (outBits.length + rest.length + 2)).cells,
        (coordinateCopyFrame coord dim out hc hd ho hcd hco hdo base
          (pre ++ rest) (outBits ++ rest.map N.bitSym)
          (pre.length + rest.length + 1) (outBits.length + rest.length + 2)).head⟩ := by
  rw [Function.iterate_succ_apply', copy_coordinate_suffix_run]
  let c := coordinateCopyFrame coord dim out hc hd ho hcd hco hdo base
    (pre ++ rest) (outBits ++ rest.map N.bitSym)
    (pre.length + rest.length + 1) (outBits.length + rest.length + 2)
  have hcell : c.cells coord (c.head coord) = N.blank := by
    simp [c, coordinateCopyFrame, MultitapeTM.tapeOf]
  have hnonbit : c.cells coord (c.head coord) ≠ N.zero ∧
      c.cells coord (c.head coord) ≠ N.one := by
    rw [hcell]
    exact ⟨blank_ne_zero, blank_ne_one⟩
  have hstep := copy_coordinate_end_step coord dim out hc hd ho hcd hco hdo
    c rfl hnonbit
  simpa [c] using hstep

private theorem skip_sign_again_step {N : MultitapeTM}
    (coord dim out : Fin N.k)
    (hc : coord ≠ N.inTape) (hd : dim ≠ N.inTape) (ho : out ≠ N.inTape)
    (hcd : coord ≠ dim) (hco : coord ≠ out) (hdo : dim ≠ out)
    (c : (control N coord dim out hc hd ho hcd hco hdo).machine.Cfg)
    (hs : c.state = State.skipSignAgain)
    (hh : c.head coord = 1) :
    (machine N coord dim out hc hd ho hcd hco hdo).step c =
      { state := State.skipHighAgain, cells := c.cells,
        head := Function.update c.head coord 2 } := by
  let P := control N coord dim out hc hd ho hcd hco hdo
  apply cfg_ext P
  · change (transition N coord dim out c.state
      (fun i => c.cells i (c.head i))).1 = State.skipHighAgain
    rw [hs]
    simp [transition, raw]
  · funext i p
    change Function.update (c.cells i) (c.head i)
      (((transition N coord dim out c.state
        (fun j => c.cells j (c.head j))).2 i).1) p = c.cells i p
    rw [hs]
    by_cases hp : p = c.head i
    · subst p
      by_cases hi : i = coord
      · subst i
        simp [transition, raw, protect_self_move]
      · simp [transition, raw, hi, protect_self_move]
    · rw [Function.update_of_ne hp]
  · funext i
    change (match ((transition N coord dim out c.state
        (fun j => c.cells j (c.head j))).2 i).2 with
      | Move.left => c.head i - 1
      | Move.stay => c.head i
      | Move.right => c.head i + 1) =
        Function.update c.head coord 2 i
    rw [hs]
    by_cases hi : i = coord
    · subst i
      simp [transition, raw, protect_self_move, hh]
    · simp [transition, raw, hi, protect_self_move]

private theorem skip_high_again_step {N : MultitapeTM}
    (coord dim out : Fin N.k)
    (hc : coord ≠ N.inTape) (hd : dim ≠ N.inTape) (ho : out ≠ N.inTape)
    (hcd : coord ≠ dim) (hco : coord ≠ out) (hdo : dim ≠ out)
    (c : (control N coord dim out hc hd ho hcd hco hdo).machine.Cfg)
    (hs : c.state = State.skipHighAgain)
    (hh : c.head coord = 2)
    (hcell : c.cells coord 2 ≠ N.startSym) :
    (machine N coord dim out hc hd ho hcd hco hdo).step c =
      { state := State.copyCoordinate, cells := c.cells,
        head := Function.update c.head coord 3 } := by
  let P := control N coord dim out hc hd ho hcd hco hdo
  apply cfg_ext P
  · change (transition N coord dim out c.state
      (fun i => c.cells i (c.head i))).1 = State.copyCoordinate
    rw [hs]
    simp [transition, raw]
  · funext i p
    change Function.update (c.cells i) (c.head i)
      (((transition N coord dim out c.state
        (fun j => c.cells j (c.head j))).2 i).1) p = c.cells i p
    rw [hs]
    by_cases hp : p = c.head i
    · subst p
      by_cases hi : i = coord
      · subst i
        simp [transition, raw, protect_self_move]
      · simp [transition, raw, hi, protect_self_move]
    · rw [Function.update_of_ne hp]
  · funext i
    change (match ((transition N coord dim out c.state
        (fun j => c.cells j (c.head j))).2 i).2 with
      | Move.left => c.head i - 1
      | Move.stay => c.head i
      | Move.right => c.head i + 1) = Function.update c.head coord 3 i
    rw [hs]
    by_cases hi : i = coord
    · subst i
      simp [transition, raw, protect_self_move, hh]
    · simp [transition, raw, hi, protect_self_move]

/-- Starting from a signed coordinate record and a parsed dimension, the
    shared-host staging controller writes `bin(q,n) ++ sep ++ low_q` and
    halts after an explicit linear number of transitions. This isolates the
    physical operand-pair handoff; parsing and multiplier execution compose
    around this run separately. -/
theorem coordinate_pair_to_halt {N : MultitapeTM}
    (coord dim out : Fin N.k)
    (hc : coord ≠ N.inTape) (hd : dim ≠ N.inTape) (ho : out ≠ N.inTape)
    (hcd : coord ≠ dim) (hco : coord ≠ out) (hdo : dim ≠ out)
    (base : (control N coord dim out hc hd ho hcd hco hdo).machine.Cfg)
    (dimension low : List Bool) (sign high : Bool)
    (hdimCells : base.cells dim = N.tapeOf (dimension.map N.bitSym))
    (hdimHead : base.head dim = dimension.length + 1)
    (hcoordCells : base.cells coord = N.tapeOf (([sign, high] ++ low).map N.bitSym))
    (hcoordHead : base.head coord = low.length + 3)
    (hq : dimension.length ≤ low.length)
    (hpad : ∀ p, 1 ≤ p →
      (N.tapeOf (N.blank :: List.replicate low.length N.zero)) p ≠ N.startSym)
    (hdimBlank : (N.tapeOf (dimension.map N.bitSym))
      (dimension.length + 1) = N.blank) :
    (machine N coord dim out hc hd ho hcd hco hdo).step^[
      2 * dimension.length + 3 * low.length + 14]
      (initialStageFrame coord dim out hc hd ho hcd hco hdo base
        ([sign, high] ++ low)) =
      ⟨State.halt,
        (coordinateCopyFrame coord dim out hc hd ho hcd hco hdo base
          ([sign, high] ++ low)
          (List.replicate (low.length - dimension.length) N.zero ++
            dimension.map N.bitSym ++ [N.sep] ++ low.map N.bitSym)
          (low.length + 3)
          ((List.replicate (low.length - dimension.length) N.zero ++
            dimension.map N.bitSym ++ [N.sep]).length + low.length + 2)).cells,
        (coordinateCopyFrame coord dim out hc hd ho hcd hco hdo base
          ([sign, high] ++ low)
          (List.replicate (low.length - dimension.length) N.zero ++
            dimension.map N.bitSym ++ [N.sep] ++ low.map N.bitSym)
          (low.length + 3)
          ((List.replicate (low.length - dimension.length) N.zero ++
            dimension.map N.bitSym ++ [N.sep]).length + low.length + 2)).head⟩ := by
  let source := [sign, high] ++ low
  let padded := List.replicate (low.length - dimension.length) N.zero ++
    dimension.map N.bitSym
  let outBits := padded ++ [N.sep]
  let staged := separatorFrame coord dim out hc hd ho hcd hco hdo base
    dimension padded (low.length - dimension.length + 2)
  have hfirst := first_operand_separator_run coord dim out hc hd ho hcd hco hdo
    base dimension low sign high hdimCells hdimHead hcoordCells hcoordHead hq hpad hdimBlank
  have hfirst' : (machine N coord dim out hc hd ho hcd hco hdo).step^[
      2 * dimension.length + low.length + 7]
      (initialStageFrame coord dim out hc hd ho hcd hco hdo base source) = staged := by
    simpa [source, staged, padded, List.append_assoc] using hfirst
  have hmarker : base.cells coord 0 = N.startSym := by
    rw [hcoordCells]
    simp [MultitapeTM.tapeOf]
  have hnonmarker : ∀ j, 1 ≤ j → base.cells coord j ≠ N.startSym := by
    intro j hj
    rw [hcoordCells]
    exact bits_tape_not_start source j hj
  have hrewstart :
      rewindFrame coord dim out hc hd ho hcd hco hdo staged (low.length + 3) = staged := by
    apply cfg_ext (control N coord dim out hc hd ho hcd hco hdo)
    · rfl
    · rfl
    · funext i
      by_cases hi : i = coord
      · subst i
        simp [rewindFrame, staged, separatorFrame, hcoordHead, hcd, hco,
          Ne.symm hcd, Ne.symm hco, Function.update]
      · simp [rewindFrame, staged, separatorFrame, hi]
  have hrew := rewind_coordinate_run coord dim out hc hd ho hcd hco hdo
    staged (low.length + 3)
    (by simpa [staged, separatorFrame, hco, hcd, hdo] using hmarker)
    (by
      intro j hj
      have hj' : (base.cells coord j) ≠ N.startSym := hnonmarker j hj
      simpa [staged, separatorFrame, hco, hcd, hdo] using hj')
  rw [hrewstart] at hrew
  let skip₁ : (control N coord dim out hc hd ho hcd hco hdo).machine.Cfg :=
    ⟨State.skipSignAgain, staged.cells, Function.update staged.head coord 1⟩
  have hskip1 : (machine N coord dim out hc hd ho hcd hco hdo).step skip₁ =
      ⟨State.skipHighAgain, staged.cells,
        Function.update staged.head coord 2⟩ := by
    have hs : skip₁.state = State.skipSignAgain := rfl
    have hh : skip₁.head coord = 1 := by simp [skip₁, Function.update]
    simpa [skip₁] using skip_sign_again_step coord dim out hc hd ho hcd hco hdo
      skip₁ hs hh
  let skip₂ : (control N coord dim out hc hd ho hcd hco hdo).machine.Cfg :=
    ⟨State.skipHighAgain, staged.cells, Function.update staged.head coord 2⟩
  have hskip2 : (machine N coord dim out hc hd ho hcd hco hdo).step skip₂ =
      ⟨State.copyCoordinate, staged.cells,
        Function.update staged.head coord 3⟩ := by
    have hs : skip₂.state = State.skipHighAgain := rfl
    have hh : skip₂.head coord = 2 := by simp [skip₂, Function.update]
    simpa [skip₂] using skip_high_again_step coord dim out hc hd ho hcd hco hdo
      skip₂ hs hh (by
        rw [show staged.cells coord 2 = base.cells coord 2 by
          simp [staged, separatorFrame, hcd, hco, hdo]]
        rw [hcoordCells]
        exact bit_symbol_not_start N high)
  have hcopyStart :
      (⟨State.copyCoordinate, staged.cells,
        Function.update staged.head coord 3⟩ :
        (control N coord dim out hc hd ho hcd hco hdo).machine.Cfg) =
      coordinateCopyFrame coord dim out hc hd ho hcd hco hdo base source outBits 3
        (outBits.length + 2) := by
    apply cfg_ext (control N coord dim out hc hd ho hcd hco hdo)
    · rfl
    · funext i p
      by_cases hiC : i = coord
      · subst i
        simp [coordinateCopyFrame, staged, separatorFrame, source,
          hcoordCells, hcd, hco, Ne.symm hcd, Ne.symm hco, List.map_append]
      · by_cases hiO : i = out
        · subst i
          simp [coordinateCopyFrame, staged, separatorFrame, outBits, padded,
            hco, hdo, hcd, Ne.symm hco, Ne.symm hdo, List.append_assoc,
            List.length_append, List.length_replicate, List.length_map,
            Nat.sub_add_cancel hq]
        · by_cases hiD : i = dim
          · subst i
            simp [coordinateCopyFrame, staged, separatorFrame, hdimCells, hdimHead,
              hco, hdo, hcd, Ne.symm hcd, Ne.symm hdo, Ne.symm hco]
          · simp [coordinateCopyFrame, staged, separatorFrame, hiC, hiO, hiD,
              hco, hdo, hcd, Ne.symm hcd, Ne.symm hdo, Ne.symm hco]
    · funext i
      by_cases hiC : i = coord
      · subst i
        simp [coordinateCopyFrame, source]
      · by_cases hiO : i = out
        · subst i
          simp [coordinateCopyFrame, outBits, staged, separatorFrame, hiC,
            padded, hco, hdo, Ne.symm hco, Ne.symm hdo, List.length_append,
            List.length_replicate, List.length_map]
          have hsub : low.length - dimension.length + dimension.length = low.length :=
            Nat.sub_add_cancel hq
          omega
        · by_cases hiD : i = dim
          · subst i
            simp [coordinateCopyFrame, staged, separatorFrame, hdimHead,
              hco, hdo, hcd, Ne.symm hcd, Ne.symm hdo, Ne.symm hco,
              Function.update]
          · simp [coordinateCopyFrame, staged, separatorFrame, hiC, hiO, hiD,
              hco, hdo, hcd, Ne.symm hco, Ne.symm hdo]
  have hprefix :
      (machine N coord dim out hc hd ho hcd hco hdo).step^[2]
        (⟨State.skipSignAgain, staged.cells,
          Function.update staged.head coord 1⟩) =
      coordinateCopyFrame coord dim out hc hd ho hcd hco hdo base source outBits 3
        (outBits.length + 2) := by
    rw [show 2 = 1 + 1 by omega, Function.iterate_add_apply,
      Function.iterate_one, hskip1, hskip2, hcopyStart]
  have hcopy := copy_coordinate_suffix_to_halt coord dim out hc hd ho hcd hco hdo
    base [sign, high] low outBits
  have hcopyHead : [sign, high].length + low.length + 1 = low.length + 3 := by
    simp
    omega
  let firstTime := 2 * dimension.length + low.length + 7
  let rewindTime := low.length + 4
  let copyTime := low.length + 1
  let initial := initialStageFrame coord dim out hc hd ho hcd hco hdo base source
  have hrewindCompose :
      (machine N coord dim out hc hd ho hcd hco hdo).step^[rewindTime + firstTime] initial =
        ⟨State.skipSignAgain, staged.cells, Function.update staged.head coord 1⟩ := by
    have hfirstT : (machine N coord dim out hc hd ho hcd hco hdo).step^[firstTime] initial = staged := by
      simpa [firstTime, initial] using hfirst'
    have hrewT : (machine N coord dim out hc hd ho hcd hco hdo).step^[rewindTime] staged =
        ⟨State.skipSignAgain, staged.cells, Function.update staged.head coord 1⟩ := by
      simpa [rewindTime] using hrew
    rw [Function.iterate_add_apply, hfirstT, hrewT]
  have hprefixCompose :
      (machine N coord dim out hc hd ho hcd hco hdo).step^[2 + rewindTime + firstTime] initial =
        coordinateCopyFrame coord dim out hc hd ho hcd hco hdo base source outBits 3
          (outBits.length + 2) := by
    have hiter :
        (machine N coord dim out hc hd ho hcd hco hdo).step^[
          2 + (rewindTime + firstTime)] initial =
        (machine N coord dim out hc hd ho hcd hco hdo).step^[2]
          ((machine N coord dim out hc hd ho hcd hco hdo).step^[rewindTime + firstTime] initial) := by
      nth_rewrite 1 [Function.iterate_add_apply]
      rfl
    have hassoc : 2 + rewindTime + firstTime = 2 + (rewindTime + firstTime) := by omega
    rw [hassoc, hiter, hrewindCompose]
    exact hprefix
  have hcopyCompose :
      (machine N coord dim out hc hd ho hcd hco hdo).step^[copyTime + (2 + rewindTime + firstTime)] initial =
        ⟨State.halt,
          (coordinateCopyFrame coord dim out hc hd ho hcd hco hdo base source
            (outBits ++ low.map N.bitSym) ([sign, high].length + low.length + 1)
            (outBits.length + low.length + 2)).cells,
          (coordinateCopyFrame coord dim out hc hd ho hcd hco hdo base source
            (outBits ++ low.map N.bitSym) ([sign, high].length + low.length + 1)
            (outBits.length + low.length + 2)).head⟩ := by
    have hiter :
        (machine N coord dim out hc hd ho hcd hco hdo).step^[
          copyTime + (2 + rewindTime + firstTime)] initial =
        (machine N coord dim out hc hd ho hcd hco hdo).step^[copyTime]
          ((machine N coord dim out hc hd ho hcd hco hdo).step^[2 + rewindTime + firstTime] initial) := by
      nth_rewrite 1 [Function.iterate_add_apply]
      rfl
    rw [hiter, hprefixCompose]
    simpa [copyTime, source, outBits, List.length_append, hcopyHead] using hcopy
  have htime : copyTime + (2 + rewindTime + firstTime) =
      2 * dimension.length + 3 * low.length + 14 := by
    simp [copyTime, rewindTime, firstTime]
    omega
  rw [← htime]
  rw [hcopyHead] at hcopyCompose
  simpa [initial, source, outBits, padded, coordinateCopyFrame,
    List.append_assoc, List.length_append, List.length_map, List.length_replicate] using hcopyCompose

end BitDFT.BankedOperandStageProof
end


noncomputable section
open IntMul BitDFT.OperandStage BitDFT.MachineSequence BitDFT.BankedOperandStageProofSupport
theorem solution {N : MultitapeTM}
    (coord dim out : Fin N.k)
    (hc : coord ≠ N.inTape) (hd : dim ≠ N.inTape) (ho : out ≠ N.inTape)
    (hcd : coord ≠ dim) (hco : coord ≠ out) (hdo : dim ≠ out)
    (base : (control N coord dim out hc hd ho hcd hco hdo).machine.Cfg)
    (dimension low : List Bool) (sign high : Bool)
    (hdimCells : base.cells dim = N.tapeOf (dimension.map N.bitSym))
    (hdimHead : base.head dim = dimension.length + 1)
    (hcoordCells : base.cells coord = N.tapeOf (([sign, high] ++ low).map N.bitSym))
    (hcoordHead : base.head coord = low.length + 3)
    (hq : dimension.length ≤ low.length)
    (hpad : ∀ p, 1 ≤ p →
      (N.tapeOf (N.blank :: List.replicate low.length N.zero)) p ≠ N.startSym)
    (hdimBlank : (N.tapeOf (dimension.map N.bitSym))
      (dimension.length + 1) = N.blank) :
    (machine N coord dim out hc hd ho hcd hco hdo).step^[
      2 * dimension.length + 3 * low.length + 14]
      (initialStageFrame coord dim out hc hd ho hcd hco hdo base
        ([sign, high] ++ low)) =
      ⟨State.halt,
        (coordinateCopyFrame coord dim out hc hd ho hcd hco hdo base
          ([sign, high] ++ low)
          (List.replicate (low.length - dimension.length) N.zero ++
            dimension.map N.bitSym ++ [N.sep] ++ low.map N.bitSym)
          (low.length + 3)
          ((List.replicate (low.length - dimension.length) N.zero ++
            dimension.map N.bitSym ++ [N.sep]).length + low.length + 2)).cells,
        (coordinateCopyFrame coord dim out hc hd ho hcd hco hdo base
          ([sign, high] ++ low)
          (List.replicate (low.length - dimension.length) N.zero ++
            dimension.map N.bitSym ++ [N.sep] ++ low.map N.bitSym)
          (low.length + 3)
          ((List.replicate (low.length - dimension.length) N.zero ++
            dimension.map N.bitSym ++ [N.sep]).length + low.length + 2)).head⟩ := by
  exact BitDFT.BankedOperandStageProof.coordinate_pair_to_halt (N := N) coord dim out hc hd ho hcd hco hdo base dimension low sign high hdimCells hdimHead hcoordCells hcoordHead hq hpad hdimBlank
end
