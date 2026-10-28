-- Prove2me | solution 1 for BitDFT.BoundaryShiftEmitter.boundary_shift_emit_run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T21:37:10.252929+00:00
-- url     : https://prove2.me/submissions/b279313f-1780-432d-9308-0e33332fb0b3

import Definitions.Def_BitDFT_BoundaryShiftEmitter
import Mathlib.Tactic
import Mathlib.Data.List.GetD

set_option autoImplicit false
set_option maxHeartbeats 0

open BitDFT.BoundaryShiftEmitter
open IntMul

private theorem cfg_ext {M : MultitapeTM} (c d : M.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c; cases d; cases hs; cases hc; cases hh; rfl

private theorem tape_append_bit (N : MultitapeTM) (out : List Bool) (b : Bool) :
    Function.update (N.tapeOf (out.map N.bitSym)) (out.length+1) (N.bitSym b) =
      N.tapeOf ((out ++ [b]).map N.bitSym) := by
  funext p
  cases p with
  | zero => simp [MultitapeTM.tapeOf]
  | succ p =>
    by_cases hp : p = out.length
    · subst p
      simp [MultitapeTM.tapeOf, List.getD_append_right]
    · rw [Function.update_of_ne (by omega : p+1 ≠ out.length+1)]
      simp only [MultitapeTM.tapeOf, List.map_append, List.map_cons, List.map_nil]
      by_cases hlt : p < out.length
      · have hlt' : p < (List.map N.bitSym out).length := by simpa using hlt
        rw [List.getD_append (List.map N.bitSym out) [N.bitSym b] N.blank p hlt']
      · have hge : out.length ≤ p := by omega
        have hge' : (List.map N.bitSym out).length ≤ p := by simpa using hge
        rw [List.getD_eq_default _ _ hge',
          List.getD_append_right (List.map N.bitSym out) [N.bitSym b] N.blank p hge']
        have hpos : 1 ≤ p - (List.map N.bitSym out).length := by
          simpa using (show 1 ≤ p - out.length by omega)
        rw [List.getD_eq_default _ _ hpos]

private theorem bit_not_start (N : MultitapeTM) (b : Bool) :
    N.bitSym b ≠ N.startSym := by
  have h := (List.pairwise_cons.mp N.syms_distinct).2
  have hs := (List.pairwise_cons.mp h).1
  have hz : N.zero ≠ N.startSym := Ne.symm (hs N.zero (by simp))
  have ho : N.one ≠ N.startSym := Ne.symm (hs N.one (by simp))
  cases b
  · exact hz
  · exact ho

private theorem tape_bit_not_start (N : MultitapeTM) (bits : List Bool) (p : ℕ)
    (hp : 0 < p) : N.tapeOf (bits.map N.bitSym) p ≠ N.startSym := by
  cases p with
  | zero => omega
  | succ p =>
    simp only [MultitapeTM.tapeOf]
    by_cases h : p < bits.length
    · rw [List.getD_eq_getElem _ _ (by simpa using h)]
      simp only [List.getElem_map]
      exact bit_not_start N _
    · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt h)]
      exact (List.pairwise_cons.mp N.syms_distinct).1 N.startSym (by simp)

private theorem tape_update_self (N : MultitapeTM) (w : List N.Sym) (p : ℕ) :
    Function.update (N.tapeOf w) p ((N.tapeOf w) p) = N.tapeOf w := by
  funext i
  by_cases h : i = p
  · subst i
    simp
  · simp [Function.update_of_ne (Ne.symm h)]

private theorem protect_self (N : MultitapeTM) (a : N.Sym) :
    protect a a .stay = (a, .stay) := by
  by_cases h : a = N.startSym <;> simp [protect, h]

@[simp] private theorem protect_right (N : MultitapeTM) (a b : N.Sym) :
    (protect a b .right).2 = .right := by
  by_cases h : a = N.startSym <;> simp [protect, h]

private theorem protect_move {N : MultitapeTM} (a b : N.Sym) (m : Move)
    (hm : m ≠ .left) : (protect a b m).2 = m := by
  by_cases h : a = N.startSym <;> simp [protect, h, hm]

private theorem protect_self_move {N : MultitapeTM} (a : N.Sym) (m : Move)
    (hm : m ≠ .left) : protect a a m = (a, m) := by
  by_cases h : a = N.startSym <;> simp [protect, h, hm]

private theorem update_at_self {N : MultitapeTM} (f : ℕ → N.Sym) (p : ℕ) :
    Function.update f p (f p) = f := by
  funext i
  by_cases h : i = p
  · subst i
    simp
  · simp [Function.update_of_ne (Ne.symm h)]

private theorem blank_not_start (N : MultitapeTM) : N.blank ≠ N.startSym := by
  have h := (List.pairwise_cons.mp N.syms_distinct).1 N.startSym (by simp)
  exact h

private theorem blank_ne_zero (N : MultitapeTM) : N.blank ≠ N.zero := by
  intro h
  have hnot := (List.nodup_cons.mp N.syms_distinct).1
  exact hnot (by simp [h])

private theorem blank_ne_one (N : MultitapeTM) : N.blank ≠ N.one := by
  intro h
  have hnot := (List.nodup_cons.mp N.syms_distinct).1
  exact hnot (by simp [h])

@[simp] private theorem snd_if_same {α β : Type} {p : Prop} [Decidable p]
    (x y : α × β) (h : x.2 = y.2) : (if p then x else y).2 = x.2 := by
  by_cases hp : p <;> simp [hp, h]

@[simp] private theorem snd_if {α β : Type} {p : Prop} [Decidable p]
    (x y : α × β) : (if p then x else y).2 = if p then x.2 else y.2 := by
  by_cases hp : p <;> simp [hp]

private theorem sign_step
    (N : MultitapeTM) (coordinate dimension output : Fin N.k)
    (hc : coordinate ≠ N.inTape) (hd : dimension ≠ N.inTape) (ho : output ≠ N.inTape)
    (hcd : coordinate ≠ dimension) (hco : coordinate ≠ output) (hdo : dimension ≠ output)
    (base : (control N coordinate dimension output hc hd ho hcd hco hdo).machine.Cfg)
    (sign high : Bool) (low dimensionBits : List Bool) :
    let C := control N coordinate dimension output hc hd ho hcd hco hdo
    C.machine.step (frame coordinate dimension output hc hd ho hcd hco hdo base
      .sign ([sign, high] ++ low) dimensionBits [] 1 1 1) =
    frame coordinate dimension output hc hd ho hcd hco hdo base
      .skipHigh ([sign, high] ++ low) dimensionBits [sign] 2 1 2 := by
  let C := control N coordinate dimension output hc hd ho hcd hco hdo
  let c₀ := frame coordinate dimension output hc hd ho hcd hco hdo base
    .sign ([sign, high] ++ low) dimensionBits [] 1 1 1
  let c₁ := frame coordinate dimension output hc hd ho hcd hco hdo base
    .skipHigh ([sign, high] ++ low) dimensionBits [sign] 2 1 2
  have hcoord : c₀.cells coordinate (c₀.head coordinate) = N.bitSym sign := by
    simp [c₀, frame, MultitapeTM.tapeOf]
  have hcoordBits : (N.tapeOf (([sign, high] ++ low).map N.bitSym)) 1 = N.bitSym sign := by
    simp [MultitapeTM.tapeOf]
  have hwrite : c₀.cells output (c₀.head output) = N.blank := by
    simp [c₀, frame, MultitapeTM.tapeOf, Ne.symm hco, Ne.symm hdo]
  have hout : Function.update (N.tapeOf []) 1 (N.bitSym sign) =
      N.tapeOf ([sign].map N.bitSym) := by
    simpa using tape_append_bit N [] sign
  change C.machine.step c₀ = c₁
  apply cfg_ext (C.machine.step c₀) c₁
  · rfl
  · funext i p
    change Function.update (c₀.cells i) (c₀.head i)
        (((transition N coordinate dimension output State.sign
          (fun j => c₀.cells j (c₀.head j))).2 i).1) p = c₁.cells i p
    by_cases hiC : i = coordinate
    · subst i
      simp only [transition, raw]
      rw [hcoord]
      simp only [c₀, c₁, frame, if_pos rfl, if_neg (Ne.symm hcd),
        if_neg (Ne.symm hco)]
      simp [protect, hcoordBits, bit_not_start]
      rw [← hcoordBits]
      exact congrArg (fun f => f p)
        (tape_update_self N (([sign, high] ++ low).map N.bitSym) 1)
    · by_cases hiO : i = output
      · subst i
        simp only [transition, raw]
        rw [hcoord, hwrite]
        simp [c₀, c₁, frame, MultitapeTM.tapeOf, protect, hout,
          bit_not_start, blank_not_start, Ne.symm hco, Ne.symm hdo]
      · simp [c₀, c₁, frame, C, transition, raw, hiC, hiO, hco, hcd, hdo,
          Ne.symm hco, Ne.symm hcd, Ne.symm hdo, protect_self]

  · funext i
    change (match ((transition N coordinate dimension output State.sign
        (fun j => c₀.cells j (c₀.head j))).2 i).2 with
      | Move.left => c₀.head i - 1
      | Move.stay => c₀.head i
      | Move.right => c₀.head i + 1) = c₁.head i
    have hmove : ∀ j, ((transition N coordinate dimension output State.sign
        (fun j => c₀.cells j (c₀.head j))).2 j).2 =
        (if j = coordinate ∨ j = output then Move.right else Move.stay) := by
      intro j
      simp only [transition, raw]
      by_cases h : j = coordinate ∨ j = output <;> simp [h, protect_move]
    rw [hmove]
    by_cases hiC : i = coordinate
    · subst i
      simp [c₀, c₁, frame, Ne.symm hco, Ne.symm hcd]
    · by_cases hiO : i = output
      · subst i
        simp [c₀, c₁, frame, Ne.symm hco, Ne.symm hdo]
      · simp [c₀, c₁, frame, hiC, hiO]


theorem skip_high_step
    (N : MultitapeTM) (coordinate dimension output : Fin N.k)
    (hc : coordinate ≠ N.inTape) (hd : dimension ≠ N.inTape) (ho : output ≠ N.inTape)
    (hcd : coordinate ≠ dimension) (hco : coordinate ≠ output) (hdo : dimension ≠ output)
    (base : (control N coordinate dimension output hc hd ho hcd hco hdo).machine.Cfg)
    (sign high : Bool) (low dimensionBits : List Bool) :
    (machine N coordinate dimension output hc hd ho hcd hco hdo).step
      (frame coordinate dimension output hc hd ho hcd hco hdo base
        .skipHigh ([sign, high] ++ low) dimensionBits [sign] 2 1 2) =
      frame coordinate dimension output hc hd ho hcd hco hdo base
        .copyDimension ([sign, high] ++ low) dimensionBits [sign] 3 1 2 := by
  let C := control N coordinate dimension output hc hd ho hcd hco hdo
  let c₀ := frame coordinate dimension output hc hd ho hcd hco hdo base
    .skipHigh ([sign, high] ++ low) dimensionBits [sign] 2 1 2
  let c₁ := frame coordinate dimension output hc hd ho hcd hco hdo base
    .copyDimension ([sign, high] ++ low) dimensionBits [sign] 3 1 2
  apply cfg_ext (C.machine.step c₀) c₁
  · rfl
  · funext i p
    change Function.update (c₀.cells i) (c₀.head i)
      (((transition N coordinate dimension output State.skipHigh
        (fun j => c₀.cells j (c₀.head j))).2 i).1) p = c₁.cells i p
    by_cases hi : i = coordinate
    · subst i
      simp [c₀, c₁, frame, transition, raw, protect_self_move, update_at_self]
    · simp [c₀, c₁, frame, transition, raw, hi, protect_self_move, update_at_self]
  · funext i
    change (match ((transition N coordinate dimension output State.skipHigh
        (fun j => c₀.cells j (c₀.head j))).2 i).2 with
      | Move.left => c₀.head i - 1
      | Move.stay => c₀.head i
      | Move.right => c₀.head i + 1) = c₁.head i
    by_cases hi : i = coordinate
    · subst i
      simp [c₀, c₁, frame, transition, raw, protect_self_move]
    · simp [c₀, c₁, frame, transition, raw, hi, protect_self_move]

theorem copy_dimension_step
    (N : MultitapeTM) (coordinate dimension output : Fin N.k)
    (hc : coordinate ≠ N.inTape) (hd : dimension ≠ N.inTape) (ho : output ≠ N.inTape)
    (hcd : coordinate ≠ dimension) (hco : coordinate ≠ output) (hdo : dimension ≠ output)
    (base : (control N coordinate dimension output hc hd ho hcd hco hdo).machine.Cfg)
    (coordWord pre : List Bool) (b : Bool) (rest out : List Bool)
    (coordHead : ℕ) :
    let C := control N coordinate dimension output hc hd ho hcd hco hdo
    C.machine.step (frame coordinate dimension output hc hd ho hcd hco hdo base
      .copyDimension coordWord (pre ++ [b] ++ rest) out coordHead (pre.length+1) (out.length+1)) =
    frame coordinate dimension output hc hd ho hcd hco hdo base
      .copyDimension coordWord (pre ++ [b] ++ rest) (out ++ [b]) coordHead
      (pre.length+2) (out.length+2) := by
  let C := control N coordinate dimension output hc hd ho hcd hco hdo
  let c₀ := frame coordinate dimension output hc hd ho hcd hco hdo base
    .copyDimension coordWord (pre ++ [b] ++ rest) out coordHead (pre.length+1) (out.length+1)
  let c₁ := frame coordinate dimension output hc hd ho hcd hco hdo base
    .copyDimension coordWord (pre ++ [b] ++ rest) (out ++ [b]) coordHead
      (pre.length+2) (out.length+2)
  have hbit : c₀.cells dimension (c₀.head dimension) = N.bitSym b := by
    simp [c₀, frame, Ne.symm hcd, MultitapeTM.tapeOf]
  have hbits : c₀.cells dimension (c₀.head dimension) = N.zero ∨
      c₀.cells dimension (c₀.head dimension) = N.one := by
    rw [hbit]
    cases b <;> simp [MultitapeTM.bitSym]
  have hnot : N.bitSym b ≠ N.startSym := bit_not_start N b
  have hout : c₀.cells output (c₀.head output) = N.blank := by
    simp [c₀, frame, MultitapeTM.tapeOf, Ne.symm hco, Ne.symm hdo]
  have happ : Function.update (N.tapeOf (out.map N.bitSym)) (out.length+1) (N.bitSym b) =
      N.tapeOf ((out ++ [b]).map N.bitSym) := by
    simpa using tape_append_bit N out b
  change C.machine.step c₀ = c₁
  apply cfg_ext (C.machine.step c₀) c₁
  · change (transition N coordinate dimension output State.copyDimension
      (fun j => c₀.cells j (c₀.head j))).1 = State.copyDimension
    simp only [transition, raw, if_pos hbits]
  · funext i p
    change Function.update (c₀.cells i) (c₀.head i)
      (((transition N coordinate dimension output State.copyDimension
        (fun j => c₀.cells j (c₀.head j))).2 i).1) p = c₁.cells i p
    simp only [transition, raw, if_pos hbits]
    by_cases hiC : i = coordinate
    · subst i
      simp [c₀, c₁, frame, hcd, hco, protect_self, update_at_self]
    · by_cases hiD : i = dimension
      · subst i
        simp [c₀, c₁, frame, Ne.symm hcd, Ne.symm hdo, hbit,
          protect_self_move, update_at_self]
      · by_cases hiO : i = output
        · subst i
          simp only [hout, hbit]
          simp [c₀, c₁, frame, Ne.symm hco, Ne.symm hdo, hbit, hout, protect,
            happ, hnot, blank_not_start]
        · simp [c₀, c₁, frame, hiC, hiD, hiO, Ne.symm hco, Ne.symm hcd,
            Ne.symm hdo, protect_self]
  · funext i
    change (match ((transition N coordinate dimension output State.copyDimension
      (fun j => c₀.cells j (c₀.head j))).2 i).2 with
      | Move.left => c₀.head i - 1
      | Move.stay => c₀.head i
      | Move.right => c₀.head i + 1) = c₁.head i
    have hmove : ∀ j, ((transition N coordinate dimension output State.copyDimension
      (fun j => c₀.cells j (c₀.head j))).2 j).2 =
      (if j = dimension ∨ j = output then Move.right else Move.stay) := by
      intro j
      simp only [transition, raw, if_pos hbits]
      by_cases hj : j = dimension ∨ j = output <;> simp [hj, protect_move]
    rw [hmove]
    by_cases hiD : i = dimension
    · subst i
      simp [c₀, c₁, frame, Ne.symm hcd, Ne.symm hdo]
    · by_cases hiO : i = output
      · subst i
        simp [c₀, c₁, frame, Ne.symm hco, Ne.symm hdo]
      · simp [c₀, c₁, frame, hiD, hiO]

theorem copy_dimension_run
    (N : MultitapeTM) (coordinate dimension output : Fin N.k)
    (hc : coordinate ≠ N.inTape) (hd : dimension ≠ N.inTape) (ho : output ≠ N.inTape)
    (hcd : coordinate ≠ dimension) (hco : coordinate ≠ output) (hdo : dimension ≠ output)
    (base : (control N coordinate dimension output hc hd ho hcd hco hdo).machine.Cfg)
    (coordWord pre remaining out : List Bool) (coordHead : ℕ) :
    (machine N coordinate dimension output hc hd ho hcd hco hdo).step^[remaining.length]
      (frame coordinate dimension output hc hd ho hcd hco hdo base .copyDimension
        coordWord (pre ++ remaining) out coordHead (pre.length+1) (out.length+1)) =
    frame coordinate dimension output hc hd ho hcd hco hdo base .copyDimension
      coordWord (pre ++ remaining) (out ++ remaining) coordHead
      ((pre ++ remaining).length+1) ((out ++ remaining).length+1) := by
  induction remaining generalizing pre out with
  | nil => simp
  | cons b rest ih =>
    rw [show (b :: rest).length = rest.length + 1 by simp, Function.iterate_succ_apply]
    have hstep := copy_dimension_step N coordinate dimension output hc hd ho hcd hco hdo
      base coordWord pre b rest out coordHead
    have hstep' : (machine N coordinate dimension output hc hd ho hcd hco hdo).step
        (frame coordinate dimension output hc hd ho hcd hco hdo base .copyDimension
          coordWord (pre ++ b :: rest) out coordHead (pre.length+1) (out.length+1)) =
        frame coordinate dimension output hc hd ho hcd hco hdo base .copyDimension
          coordWord (pre ++ b :: rest) (out ++ [b]) coordHead
          ((pre ++ [b]).length+1) ((out ++ [b]).length+1) := by
      simpa [List.append_assoc] using hstep
    rw [hstep']
    simpa [List.append_assoc, List.length_append] using
      (ih (pre := pre ++ [b]) (out := out ++ [b]))

theorem copy_dimension_end_step
    (N : MultitapeTM) (coordinate dimension output : Fin N.k)
    (hc : coordinate ≠ N.inTape) (hd : dimension ≠ N.inTape) (ho : output ≠ N.inTape)
    (hcd : coordinate ≠ dimension) (hco : coordinate ≠ output) (hdo : dimension ≠ output)
    (base : (control N coordinate dimension output hc hd ho hcd hco hdo).machine.Cfg)
    (coordWord dimensionPrefix dimensionRest out : List Bool)
    (coordHead : ℕ) (outHead : ℕ)
    (hblank : (N.tapeOf ((dimensionPrefix ++ dimensionRest).map N.bitSym))
      (dimensionPrefix.length+1) = N.blank) :
    let C := control N coordinate dimension output hc hd ho hcd hco hdo
    C.machine.step (frame coordinate dimension output hc hd ho hcd hco hdo base
      .copyDimension coordWord (dimensionPrefix ++ dimensionRest) out coordHead
      (dimensionPrefix.length+1) outHead) =
    frame coordinate dimension output hc hd ho hcd hco hdo base
      .writeZeros coordWord (dimensionPrefix ++ dimensionRest) out coordHead
      (dimensionPrefix.length+1) outHead := by
  let C := control N coordinate dimension output hc hd ho hcd hco hdo
  let c := frame coordinate dimension output hc hd ho hcd hco hdo base
    .copyDimension coordWord (dimensionPrefix ++ dimensionRest) out coordHead
    (dimensionPrefix.length+1) outHead
  have hscan : c.cells dimension (c.head dimension) = N.blank := by
    simpa [c, frame, Ne.symm hcd, Ne.symm hdo] using hblank
  have hblankBits : c.cells dimension (c.head dimension) ≠ N.zero ∧
      c.cells dimension (c.head dimension) ≠ N.one := by
    rw [hscan]
    exact ⟨blank_ne_zero N, blank_ne_one N⟩
  have hnot : c.cells dimension (c.head dimension) ≠ N.startSym := by
    rw [hscan]
    exact blank_not_start N
  have hnonbit : ¬(c.cells dimension (c.head dimension) = N.zero ∨
      c.cells dimension (c.head dimension) = N.one) := by
    intro h
    cases h with
    | inl hz => exact hblankBits.1 hz
    | inr ho => exact hblankBits.2 ho
  apply cfg_ext (C.machine.step c)
  · change (transition N coordinate dimension output State.copyDimension
      (fun j => c.cells j (c.head j))).1 = State.writeZeros
    simp [transition, raw, hblankBits]
  · funext i p
    change Function.update (c.cells i) (c.head i)
      (((transition N coordinate dimension output State.copyDimension
        (fun j => c.cells j (c.head j))).2 i).1) p = _
    simp only [transition, raw, if_neg hnonbit]
    simp [c, frame, protect_self]
  · funext i
    change (match ((transition N coordinate dimension output State.copyDimension
      (fun j => c.cells j (c.head j))).2 i).2 with
      | Move.left => c.head i - 1
      | Move.stay => c.head i
      | Move.right => c.head i + 1) = _
    simp only [transition, raw, if_neg hnonbit]
    simp [c, frame, protect_self]

theorem write_zero_step
    (N : MultitapeTM) (coordinate dimension output : Fin N.k)
    (hc : coordinate ≠ N.inTape) (hd : dimension ≠ N.inTape) (ho : output ≠ N.inTape)
    (hcd : coordinate ≠ dimension) (hco : coordinate ≠ output) (hdo : dimension ≠ output)
    (base : (control N coordinate dimension output hc hd ho hcd hco hdo).machine.Cfg)
    (pre coordRest dimensionWord out : List Bool) (b : Bool)
    (coordHead dimHead : ℕ) :
    let C := control N coordinate dimension output hc hd ho hcd hco hdo
    C.machine.step (frame coordinate dimension output hc hd ho hcd hco hdo base
      .writeZeros (pre ++ [b] ++ coordRest) dimensionWord out
      (pre.length+1) dimHead (out.length+1)) =
    frame coordinate dimension output hc hd ho hcd hco hdo base
      .writeZeros (pre ++ [b] ++ coordRest) dimensionWord (out ++ [false])
      (pre.length+2) dimHead (out.length+2) := by
  let C := control N coordinate dimension output hc hd ho hcd hco hdo
  let c₀ := frame coordinate dimension output hc hd ho hcd hco hdo base
    .writeZeros (pre ++ [b] ++ coordRest) dimensionWord out
    (pre.length+1) dimHead (out.length+1)
  let c₁ := frame coordinate dimension output hc hd ho hcd hco hdo base
    .writeZeros (pre ++ [b] ++ coordRest) dimensionWord (out ++ [false])
    (pre.length+2) dimHead (out.length+2)
  have hbit : c₀.cells coordinate (c₀.head coordinate) = N.bitSym b := by
    simp [c₀, frame, Ne.symm hcd, MultitapeTM.tapeOf]
  have hbits : c₀.cells coordinate (c₀.head coordinate) = N.zero ∨
      c₀.cells coordinate (c₀.head coordinate) = N.one := by
    rw [hbit]
    cases b <;> simp [MultitapeTM.bitSym]
  have hout : c₀.cells output (c₀.head output) = N.blank := by
    simp [c₀, frame, Ne.symm hco, Ne.symm hdo, MultitapeTM.tapeOf]
  have happ : Function.update (N.tapeOf (out.map N.bitSym)) (out.length+1) N.zero =
      N.tapeOf ((out ++ [false]).map N.bitSym) := by
    simpa [MultitapeTM.bitSym] using tape_append_bit N out false
  have hnot : N.bitSym b ≠ N.startSym := bit_not_start N b
  have hzero : N.zero ≠ N.startSym := by
    simpa [MultitapeTM.bitSym] using bit_not_start N false
  apply cfg_ext (C.machine.step c₀)
  · change (transition N coordinate dimension output State.writeZeros
      (fun j => c₀.cells j (c₀.head j))).1 = State.writeZeros
    simp only [transition, raw, if_pos hbits]
  · funext i p
    change Function.update (c₀.cells i) (c₀.head i)
      (((transition N coordinate dimension output State.writeZeros
        (fun j => c₀.cells j (c₀.head j))).2 i).1) p = c₁.cells i p
    simp only [transition, raw, if_pos hbits]
    by_cases hiC : i = coordinate
    · subst i
      simp [c₀, c₁, frame, hcd, hco, protect_self_move, update_at_self]
    · by_cases hiD : i = dimension
      · subst i
        simp [c₀, c₁, frame, Ne.symm hcd, hdo, protect_self, update_at_self]
      · by_cases hiO : i = output
        · subst i
          simp only [hout, hbit]
          simp [c₀, c₁, frame, Ne.symm hco, Ne.symm hdo, hbit, hout,
            happ, hnot, hzero, blank_not_start, protect]
        · simp [c₀, c₁, frame, hiC, hiD, hiO, Ne.symm hcd, Ne.symm hco,
            Ne.symm hdo, protect_self]
  · funext i
    change (match ((transition N coordinate dimension output State.writeZeros
      (fun j => c₀.cells j (c₀.head j))).2 i).2 with
      | Move.left => c₀.head i - 1
      | Move.stay => c₀.head i
      | Move.right => c₀.head i + 1) = c₁.head i
    have hmove : ∀ j, ((transition N coordinate dimension output State.writeZeros
      (fun j => c₀.cells j (c₀.head j))).2 j).2 =
      (if j = coordinate ∨ j = output then Move.right else Move.stay) := by
      intro j
      simp only [transition, raw, if_pos hbits]
      by_cases hj : j = coordinate ∨ j = output <;> simp [hj, protect_move]
    rw [hmove]
    by_cases hiC : i = coordinate
    · subst i
      simp [c₀, c₁, frame, hcd, hco]
    · by_cases hiO : i = output
      · subst i
        simp [c₀, c₁, frame, Ne.symm hco, Ne.symm hdo]
      · simp [c₀, c₁, frame, hiC, hiO]

theorem write_zero_run
    (N : MultitapeTM) (coordinate dimension output : Fin N.k)
    (hc : coordinate ≠ N.inTape) (hd : dimension ≠ N.inTape) (ho : output ≠ N.inTape)
    (hcd : coordinate ≠ dimension) (hco : coordinate ≠ output) (hdo : dimension ≠ output)
    (base : (control N coordinate dimension output hc hd ho hcd hco hdo).machine.Cfg)
    (coordWord pre remaining dimensionWord out : List Bool) (dimHead : ℕ) :
    (machine N coordinate dimension output hc hd ho hcd hco hdo).step^[remaining.length]
      (frame coordinate dimension output hc hd ho hcd hco hdo base .writeZeros
        (pre ++ remaining) dimensionWord out (pre.length+1) dimHead (out.length+1)) =
    frame coordinate dimension output hc hd ho hcd hco hdo base .writeZeros
      (pre ++ remaining) dimensionWord (out ++ List.replicate remaining.length false)
      (pre.length+remaining.length+1) dimHead
      (out.length+remaining.length+1) := by
  induction remaining generalizing pre out with
  | nil => simp
  | cons b rest ih =>
    rw [show (b :: rest).length = rest.length + 1 by simp, Function.iterate_succ_apply]
    have hstep := write_zero_step N coordinate dimension output hc hd ho hcd hco hdo
      base pre rest dimensionWord out b (pre.length+1) dimHead
    have hstep' : (machine N coordinate dimension output hc hd ho hcd hco hdo).step
        (frame coordinate dimension output hc hd ho hcd hco hdo base .writeZeros
          (pre ++ b :: rest) dimensionWord out (pre.length+1) dimHead (out.length+1)) =
        frame coordinate dimension output hc hd ho hcd hco hdo base .writeZeros
          (pre ++ b :: rest) dimensionWord (out ++ [false]) (pre.length+1+1) dimHead
          (out.length+1+1) := by
      simpa [List.append_assoc] using hstep
    rw [hstep']
    simpa [List.append_assoc, List.length_append, List.replicate_succ,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (ih (pre := pre ++ [b]) (out := out ++ [false]))

theorem write_zero_end_step
    (N : MultitapeTM) (coordinate dimension output : Fin N.k)
    (hc : coordinate ≠ N.inTape) (hd : dimension ≠ N.inTape) (ho : output ≠ N.inTape)
    (hcd : coordinate ≠ dimension) (hco : coordinate ≠ output) (hdo : dimension ≠ output)
    (base : (control N coordinate dimension output hc hd ho hcd hco hdo).machine.Cfg)
    (coordPrefix coordRest dimensionWord out : List Bool)
    (dimHead outHead : ℕ)
    (hblank : (N.tapeOf ((coordPrefix ++ coordRest).map N.bitSym))
      (coordPrefix.length+1) = N.blank) :
    let C := control N coordinate dimension output hc hd ho hcd hco hdo
    C.machine.step (frame coordinate dimension output hc hd ho hcd hco hdo base
      .writeZeros (coordPrefix ++ coordRest) dimensionWord out (coordPrefix.length+1) dimHead outHead) =
    frame coordinate dimension output hc hd ho hcd hco hdo base
      .halt (coordPrefix ++ coordRest) dimensionWord out (coordPrefix.length+1) dimHead outHead := by
  let C := control N coordinate dimension output hc hd ho hcd hco hdo
  let c := frame coordinate dimension output hc hd ho hcd hco hdo base
    .writeZeros (coordPrefix ++ coordRest) dimensionWord out (coordPrefix.length+1) dimHead outHead
  have hscan : c.cells coordinate (c.head coordinate) = N.blank := by
    simpa [c, frame, Ne.symm hcd, Ne.symm hco] using hblank
  have hnonbit : ¬(c.cells coordinate (c.head coordinate) = N.zero ∨
      c.cells coordinate (c.head coordinate) = N.one) := by
    rw [hscan]
    intro h
    cases h with
    | inl hz => exact blank_ne_zero N hz
    | inr ho => exact blank_ne_one N ho
  apply cfg_ext (C.machine.step c)
  · change (transition N coordinate dimension output State.writeZeros
      (fun j => c.cells j (c.head j))).1 = State.halt
    simp only [transition, raw, if_neg hnonbit]
  · funext i p
    change Function.update (c.cells i) (c.head i)
      (((transition N coordinate dimension output State.writeZeros
        (fun j => c.cells j (c.head j))).2 i).1) p = _
    simp only [transition, raw, if_neg hnonbit]
    simp [c, frame, protect_self]
  · funext i
    change (match ((transition N coordinate dimension output State.writeZeros
      (fun j => c.cells j (c.head j))).2 i).2 with
      | Move.left => c.head i - 1
      | Move.stay => c.head i
      | Move.right => c.head i + 1) = _
    simp only [transition, raw, if_neg hnonbit]
    simp [c, frame, protect_self]

theorem solution
    (N : MultitapeTM) (coordinate dimension output : Fin N.k)
    (hc : coordinate ≠ N.inTape) (hd : dimension ≠ N.inTape) (ho : output ≠ N.inTape)
    (hcd : coordinate ≠ dimension) (hco : coordinate ≠ output) (hdo : dimension ≠ output)
    (base : (control N coordinate dimension output hc hd ho hcd hco hdo).machine.Cfg)
    (sign high : Bool) (dimensionBits low : List Bool) :
    let C := control N coordinate dimension output hc hd ho hcd hco hdo
    let initial := frame coordinate dimension output hc hd ho hcd hco hdo base
      .sign ([sign,high] ++ low) dimensionBits [] 1 1 1
    let final := frame coordinate dimension output hc hd ho hcd hco hdo base
      .halt ([sign,high] ++ low) dimensionBits
      ([sign] ++ dimensionBits ++ List.replicate low.length false)
      (low.length+3) (dimensionBits.length+1)
      (dimensionBits.length+low.length+2)
    C.machine.step^[dimensionBits.length+low.length+4] initial = final := by
  let M := machine N coordinate dimension output hc hd ho hcd hco hdo
  let initial := frame coordinate dimension output hc hd ho hcd hco hdo base
    .sign ([sign,high] ++ low) dimensionBits [] 1 1 1
  let afterSign := frame coordinate dimension output hc hd ho hcd hco hdo base
    .skipHigh ([sign,high] ++ low) dimensionBits [sign] 2 1 2
  let afterSkip := frame coordinate dimension output hc hd ho hcd hco hdo base
    .copyDimension ([sign,high] ++ low) dimensionBits [sign] 3 1 2
  let afterDimension := frame coordinate dimension output hc hd ho hcd hco hdo base
    .copyDimension ([sign,high] ++ low) dimensionBits ([sign] ++ dimensionBits)
      3 (dimensionBits.length+1) (dimensionBits.length+2)
  let afterDimensionEnd := frame coordinate dimension output hc hd ho hcd hco hdo base
    .writeZeros ([sign,high] ++ low) dimensionBits ([sign] ++ dimensionBits)
      3 (dimensionBits.length+1) (dimensionBits.length+2)
  let afterZeros := frame coordinate dimension output hc hd ho hcd hco hdo base
    .writeZeros ([sign,high] ++ low) dimensionBits
      ([sign] ++ dimensionBits ++ List.replicate low.length false)
      (low.length+3) (dimensionBits.length+1) (dimensionBits.length+low.length+2)
  let final := frame coordinate dimension output hc hd ho hcd hco hdo base
    .halt ([sign,high] ++ low) dimensionBits
    ([sign] ++ dimensionBits ++ List.replicate low.length false)
    (low.length+3) (dimensionBits.length+1)
    (dimensionBits.length+low.length+2)
  change M.step^[dimensionBits.length+low.length+4] initial = final
  have hsign : M.step initial = afterSign := by
    simpa [M, initial, afterSign] using
      sign_step N coordinate dimension output hc hd ho hcd hco hdo base sign high low dimensionBits
  have hskip : M.step afterSign = afterSkip := by
    simpa [M, afterSign, afterSkip] using
      skip_high_step N coordinate dimension output hc hd ho hcd hco hdo base sign high low dimensionBits
  have htwo : M.step^[2] initial = afterSkip := by
    rw [show 2 = 1+1 by omega, Function.iterate_add_apply]
    simp only [Function.iterate_one]
    rw [hsign, hskip]
  have hcopy : M.step^[dimensionBits.length] afterSkip = afterDimension := by
    simpa [M, afterSkip, afterDimension, List.append_assoc] using
      copy_dimension_run N coordinate dimension output hc hd ho hcd hco hdo base
        ([sign,high] ++ low) [] dimensionBits [sign] 3
  have hprefix : M.step^[dimensionBits.length+2] initial = afterDimension := by
    rw [Function.iterate_add_apply]
    rw [htwo]
    exact hcopy
  have hdimBlank : (N.tapeOf (dimensionBits.map N.bitSym))
      (dimensionBits.length+1) = N.blank := by
    simp [MultitapeTM.tapeOf]
  have hdimEnd : M.step afterDimension = afterDimensionEnd := by
    simpa [M, afterDimension, afterDimensionEnd] using
      copy_dimension_end_step N coordinate dimension output hc hd ho hcd hco hdo base
        ([sign,high] ++ low) dimensionBits [] ([sign] ++ dimensionBits) 3
        (dimensionBits.length+2) (by simpa using hdimBlank)
  have hprefixEnd : M.step^[dimensionBits.length+3] initial = afterDimensionEnd := by
    rw [show dimensionBits.length+3 = (dimensionBits.length+2)+1 by omega,
      Function.iterate_succ_apply']
    rw [hprefix, hdimEnd]
  have hzeros : M.step^[low.length+(dimensionBits.length+3)] initial = afterZeros := by
    rw [Function.iterate_add_apply]
    rw [hprefixEnd]
    simpa [M, afterDimensionEnd, afterZeros, List.append_assoc, Nat.add_assoc,
      Nat.add_left_comm, Nat.add_comm] using
      write_zero_run N coordinate dimension output hc hd ho hcd hco hdo base
        ([sign,high] ++ low) [sign,high] low dimensionBits
        ([sign] ++ dimensionBits) (dimensionBits.length+1)
  have hcoordBlank : (N.tapeOf (([sign,high] ++ low).map N.bitSym))
      (([sign,high] ++ low).length+1) = N.blank := by
    simp [MultitapeTM.tapeOf]
  have hhalt : M.step afterZeros = final := by
    simpa [M, afterZeros, final, List.append_assoc, Nat.add_assoc] using
      write_zero_end_step N coordinate dimension output hc hd ho hcd hco hdo base
        ([sign,high] ++ low) [] dimensionBits
        ([sign] ++ dimensionBits ++ List.replicate low.length false)
        (dimensionBits.length+1) (dimensionBits.length+low.length+2)
        (by simpa [List.append_assoc] using hcoordBlank)
  rw [show dimensionBits.length+low.length+4 =
      (dimensionBits.length+low.length+3)+1 by omega, Function.iterate_succ_apply']
  have hnum : dimensionBits.length+low.length+3 =
      low.length+(dimensionBits.length+3) := by omega
  rw [hnum, hzeros, hhalt]

