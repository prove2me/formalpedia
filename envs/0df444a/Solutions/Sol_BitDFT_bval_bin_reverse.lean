-- Prove2me | solution 1 for BitDFT.bval_bin_reverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T01:40:43.386401+00:00
-- url     : https://prove2.me/submissions/2288fe9c-9c29-422f-a3a9-788810418af7

import Mathlib
import Definitions.Def_IntMul_MultitapeModel
import Definitions.Def_BitDFT_bval

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section

namespace UnpackBits

open IntMul

/-- Value of a list of bits read least-significant-bit first. -/
def bval : List Bool → ℕ
  | [] => 0
  | b :: l => b.toNat + 2 * bval l

theorem bval_cons (b : Bool) (l : List Bool) : bval (b :: l) = b.toNat + 2 * bval l := rfl

theorem bval_snoc (l : List Bool) (b : Bool) :
    bval (l ++ [b]) = bval l + b.toNat * 2 ^ l.length := by
  induction l with
  | nil => simp [bval]
  | cons a t ih =>
    rw [List.cons_append, bval_cons, ih, bval_cons, List.length_cons, Nat.pow_succ]; ring

theorem bval_append (a b : List Bool) :
    bval (a ++ b) = bval a + 2 ^ a.length * bval b := by
  induction a with
  | nil => simp [bval]
  | cons x t ih =>
    rw [List.cons_append, bval_cons, ih, bval_cons, List.length_cons, Nat.pow_succ]; ring

theorem bval_lt (l : List Bool) : bval l < 2 ^ l.length := by
  induction l with
  | nil => simp [bval]
  | cons a t ih =>
    rw [bval_cons, List.length_cons, Nat.pow_succ]
    have h : a.toNat ≤ 1 := by cases a <;> simp
    nlinarith

theorem bval_inj {l l' : List Bool} (h : l.length = l'.length) (hv : bval l = bval l') :
    l = l' := by
  induction l generalizing l' with
  | nil =>
    cases l' with
    | nil => rfl
    | cons _ _ => simp at h
  | cons a t ih =>
    cases l' with
    | nil => simp at h
    | cons a' t' =>
      simp only [bval_cons, List.length_cons] at hv h
      have ha : a.toNat ≤ 1 := by cases a <;> simp
      have ha' : a'.toNat ≤ 1 := by cases a' <;> simp
      have h1 : a.toNat = a'.toNat := by
        have hlt := bval_lt t
        have hlt' := bval_lt t'
        omega
      have h2 : bval t = bval t' := by
        have hlt := bval_lt t
        have hlt' := bval_lt t'
        omega
      have hab : a = a' := by cases a <;> cases a' <;> simp_all
      subst hab
      rw [ih (by omega) h2]

theorem bin_succ (k z : ℕ) : IntMul.bin (k + 1) z = z.testBit k :: IntMul.bin k z := by
  have hfun : (fun i : Fin k => z.testBit (k + 1 - 1 - ((Fin.succ i : Fin (k + 1)) : ℕ))) =
      (fun i : Fin k => z.testBit (k - 1 - i)) := by
    funext i
    congr 1
    have hi := i.isLt
    simp [Fin.val_succ]
    omega
  rw [show IntMul.bin (k + 1) z
      = List.ofFn (fun i : Fin (k + 1) => z.testBit (k + 1 - 1 - i)) from rfl, List.ofFn_succ,
    hfun]
  rfl

theorem testBit_toNat (z k : ℕ) : (z.testBit k).toNat = z / 2 ^ k % 2 := by
  have h2 : z / 2 ^ k % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have h3 : z / 2 ^ k % 2 = 0 ∨ z / 2 ^ k % 2 = 1 := by omega
  rw [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.one_and_eq_mod_two]
  rcases h3 with h | h <;> rw [h] <;> rfl

theorem mod_pow_succ (z k : ℕ) : z % 2 ^ (k + 1) = z % 2 ^ k + (z / 2 ^ k % 2) * 2 ^ k := by
  set c := 2 ^ k with hc
  set q := z / c with hq
  set r := z % c with hr
  have hdiv : q = 2 * (q / 2) + q % 2 := (Nat.div_add_mod q 2).symm
  have h1 : z = c * q + r := (Nat.div_add_mod z c).symm
  have hlt : r < c := by rw [hr, hc]; exact Nat.mod_lt _ (Nat.two_pow_pos k)
  have he2 : q % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have hz : z = (c * (q % 2) + r) + (c * 2) * (q / 2) := by
    have step : (c * (q % 2) + r) + (c * 2) * (q / 2) = c * q + r := by
      calc (c * (q % 2) + r) + (c * 2) * (q / 2)
          = c * (2 * (q / 2) + q % 2) + r := by ring
        _ = c * q + r := by rw [← hdiv]
    rw [step]; exact h1
  have hlt2 : c * (q % 2) + r < c * 2 := by nlinarith
  rw [show (2 : ℕ) ^ (k + 1) = c * 2 by rw [hc, Nat.pow_succ], hz, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt hlt2]
  ring

/-- `(bin k z).reverse` is the low bits of `z`, least significant first. -/
theorem bval_bin_reverse (k z : ℕ) : bval (IntMul.bin k z).reverse = z % 2 ^ k := by
  induction k generalizing z with
  | zero => simp [IntMul.bin, bval, Nat.mod_one]
  | succ k ih =>
    rw [bin_succ, List.reverse_cons, bval_snoc, ih, List.length_reverse,
      show (IntMul.bin k z).length = k from by simp [IntMul.bin], testBit_toNat]
    exact (mod_pow_succ z k).symm

/-- Add a carry bit to a bit list (least significant first); returns the sum and the carry out. -/
def addC : Bool → List Bool → List Bool × Bool
  | κ, [] => ([], κ)
  | κ, x :: t => ((x != κ) :: (addC (x && κ) t).1, (addC (x && κ) t).2)

theorem bval_addC (κ : Bool) (l : List Bool) :
    bval (addC κ l).1 + (addC κ l).2.toNat * 2 ^ l.length = bval l + κ.toNat := by
  induction l generalizing κ with
  | nil => cases κ <;> simp [addC, bval]
  | cons x t ih =>
    simp only [addC, bval_cons, List.length_cons, Nat.pow_succ]
    have h := ih (x && κ)
    have hx : (x != κ).toNat + 2 * (x && κ).toNat = x.toNat + κ.toNat := by
      cases x <;> cases κ <;> simp
    cases hc : (addC (x && κ) t).2 <;>
      simp only [hc, Bool.toNat_true, Bool.toNat_false, Nat.one_mul, Nat.zero_mul,
        Nat.add_zero] at h ⊢ <;> omega

/-- Flip every bit when `g` is true. -/
def flipB (g : Bool) (l : List Bool) : List Bool := l.map (fun b => b != g)

theorem flipB_false (l : List Bool) : flipB false l = l := by simp [flipB]

theorem bval_flipB_true_add (l : List Bool) :
    bval (flipB true l) + bval l + 1 = 2 ^ l.length := by
  induction l with
  | nil => simp [flipB, bval]
  | cons x t ih =>
    have hx : (x != true).toNat + x.toNat = 1 := by cases x <;> simp
    have hstep : flipB true (x :: t) = (x != true) :: flipB true t := rfl
    rw [hstep, bval_cons, bval_cons, List.length_cons, Nat.pow_succ]
    omega

theorem bval_flipB_true (l : List Bool) :
    bval (flipB true l) = 2 ^ l.length - 1 - bval l := by
  have := bval_flipB_true_add l; omega

theorem bval_flipB_false (l : List Bool) : bval (flipB false l) = bval l := by
  rw [flipB_false]

/-- Two's complement of a bit list with flip bit `g` (identity when `g` is false). -/
def twosC (g : Bool) (l : List Bool) : List Bool × Bool := addC g (flipB g l)

theorem bval_twosC_false (l : List Bool) : bval (twosC false l).1 = bval l := by
  show bval (addC false (flipB false l)).1 = bval l
  have hlen : (flipB false l).length = l.length := by simp [flipB]
  have h := bval_addC false (flipB false l)
  rw [bval_flipB_false, hlen] at h
  simp only [Bool.toNat_false, Nat.add_zero, Nat.zero_mul, Nat.add_zero] at h
  cases hc : (addC false (flipB false l)).2
  · simpa [hc] using h
  · simp only [hc, Bool.toNat_true, Nat.one_mul] at h
    have := bval_lt l; omega

theorem bval_twosC_true_add (l : List Bool) (hpos : 0 < bval l) :
    bval (twosC true l).1 + bval l = 2 ^ l.length := by
  show bval (addC true (flipB true l)).1 + bval l = 2 ^ l.length
  have h := bval_addC true (flipB true l)
  have hf := bval_flipB_true_add l
  have h2 : (flipB true l).length = l.length := by simp [flipB]
  rw [h2] at h
  have key : bval (addC true (flipB true l)).1 +
      (addC true (flipB true l)).2.toNat * 2 ^ l.length + bval l = 2 ^ l.length := by
    rw [h]
    calc (bval (flipB true l) + 1) + bval l = bval (flipB true l) + bval l + 1 := by ring
      _ = 2 ^ l.length := hf
  cases hc : (addC true (flipB true l)).2
  · simp only [hc, Bool.toNat_false, Nat.zero_mul, Nat.add_zero] at key ⊢
    exact key
  · simp only [hc, Bool.toNat_true, Nat.one_mul] at key ⊢
    omega

theorem bval_twosC_true (l : List Bool) (hpos : 0 < bval l) :
    bval (twosC true l).1 = 2 ^ l.length - bval l := by
  have := bval_twosC_true_add l hpos; omega

theorem bval_drop_one (l : List Bool) : bval (l.drop 1) = bval l / 2 := by
  cases l with
  | nil => simp [bval]
  | cons b t =>
    simp only [List.drop_one, List.tail_cons, bval_cons]
    have hb : b.toNat ≤ 1 := by cases b <;> simp
    omega

theorem bval_drop (l : List Bool) (j : ℕ) : bval (l.drop j) = bval l / 2 ^ j := by
  induction j generalizing l with
  | zero => simp
  | succ j ih =>
    rw [show l.drop (j + 1) = (l.drop 1).drop j by rw [List.drop_drop, Nat.add_comm], ih (l.drop 1),
      bval_drop_one, Nat.pow_succ, Nat.div_div_eq_div_mul, Nat.mul_comm]

theorem bval_split (l : List Bool) (j : ℕ) :
    bval l = bval (l.take j) + 2 ^ j * bval (l.drop j) := by
  induction l generalizing j with
  | nil => simp [bval]
  | cons b t ih =>
    cases j with
    | zero => simp [bval]
    | succ j =>
      rw [bval_cons, ih j, List.take_succ_cons, List.drop_succ_cons, bval_cons, Nat.pow_succ]
      ring

theorem bval_take (l : List Bool) (j : ℕ) : bval (l.take j) = bval l % 2 ^ j := by
  have h := bval_split l j
  have h1 : bval (l.take j) < 2 ^ j := by
    have h2 := bval_lt (l.take j)
    have h3 : (l.take j).length ≤ j := by simp
    have h4 : 2 ^ (l.take j).length ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) h3
    omega
  rw [h, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h1]

/-- The `i`-th chunk of `k` bits of a least-significant-first bit list. -/
def chunk (k : ℕ) (l : List Bool) (i : ℕ) : List Bool := (l.drop (i * k)).take k

theorem bval_chunk (l : List Bool) (k i : ℕ) :
    bval (chunk k l i) = bval l / 2 ^ (i * k) % 2 ^ k := by
  rw [chunk, bval_take, bval_drop]

end UnpackBits

/-! Bridge from the local bit value to the published one. -/

theorem bval_eq (l : List Bool) : UnpackBits.bval l = BitDFT.bval l := by
  induction l with
  | nil => rfl
  | cons b t ih => rw [UnpackBits.bval_cons, BitDFT.bval_cons, ih]


open UnpackBits

theorem solution (k z : ℕ) : BitDFT.bval (IntMul.bin k z).reverse = z % 2 ^ k := by
  rw [← bval_eq]
  exact UnpackBits.bval_bin_reverse k z
