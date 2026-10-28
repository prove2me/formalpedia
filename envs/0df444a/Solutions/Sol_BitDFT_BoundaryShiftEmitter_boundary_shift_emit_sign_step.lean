-- Prove2me | solution 1 for BitDFT.BoundaryShiftEmitter.boundary_shift_emit_sign_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T21:18:52.403157+00:00
-- url     : https://prove2.me/submissions/7a084c49-f645-4a79-a627-9f2b8e366a01

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

private theorem blank_not_start (N : MultitapeTM) : N.blank ≠ N.startSym := by
  have h := (List.pairwise_cons.mp N.syms_distinct).1 N.startSym (by simp)
  exact h

@[simp] private theorem snd_if_same {α β : Type} {p : Prop} [Decidable p]
    (x y : α × β) (h : x.2 = y.2) : (if p then x else y).2 = x.2 := by
  by_cases hp : p <;> simp [hp, h]

@[simp] private theorem snd_if {α β : Type} {p : Prop} [Decidable p]
    (x y : α × β) : (if p then x else y).2 = if p then x.2 else y.2 := by
  by_cases hp : p <;> simp [hp]

theorem solution
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



