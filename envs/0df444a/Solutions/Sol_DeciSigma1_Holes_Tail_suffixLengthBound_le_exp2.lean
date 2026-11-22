-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.suffixLengthBound_le_exp2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:07:30.816586+00:00
-- url     : https://prove2.me/submissions/53457e37-9ffe-4ddb-9aaf-bfd79455aa3f

module
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_ElementaryBounds
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Levels
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_LevelElementaryBound
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_cons_cons
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_nil
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_singleton
public import Theorems.Thm_DeciSigma1_Arithmetic_exp2_add
public import Theorems.Thm_DeciSigma1_Arithmetic_exp2_mono
public import Theorems.Thm_DeciSigma1_Arithmetic_exp2_mul
public import Theorems.Thm_DeciSigma1_Arithmetic_le_exp2
public import Theorems.Thm_DeciSigma1_Arithmetic_succ_le_exp2
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Tail_le_iterate_of_le_self
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthBound_cons
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthBound_nil
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthEnvelope_nil
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_trans
public import Theorems.Thm_DeciSigma1_Words_Ray_length_suffixBeforeOnset
public import Theorems.Thm_DeciSigma1_Words_length_suffixOfLength
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_cons_cons
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_nil
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_singleton
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.Holes.Tail.suffixLengthBound_nil
attribute [local simp] DeciSigma1.Holes.Tail.suffixLengthEnvelope_nil
attribute [local simp] DeciSigma1.Words.Ray.length_suffixBeforeOnset
attribute [local simp] DeciSigma1.Words.length_suffixOfLength
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc


section
@[expose] public section
namespace DeciSigma1.Holes.Tail
open Arithmetic
private theorem exp2_pos (t : ℕ) : 0 < exp2 t := by
  exact Nat.two_pow_pos t
private theorem exponent_pos {b t : ℕ} (hb : b + 2 ≤ exp2 t) : 1 ≤ t := by
  by_contra h
  have : t = 0 := by omega
  simp [this, exp2] at hb
private theorem base_log_bound (m N b t : ℕ) (hb : b + 2 ≤ exp2 t) :
    suffixLengthBound m N [] b + b + 2 ≤ exp2 (exp2 (m + N + 10) * t) := by
  have ht := exponent_pos hb
  let B := exp2 t
  have hB : 1 ≤ B := exp2_pos t
  have hm := succ_le_exp2 m
  have hN := le_exp2 N
  have hd : b * (b + 1) / 2 ≤ B * B :=
    (Nat.div_le_self _ _).trans (Nat.mul_le_mul (by omega) (by omega))
  have hnode : m * (b * (b + 1) / 2) + 1 ≤ (m + 1) * (B * B) := by
    have := Nat.mul_le_mul_left m hd
    nlinarith
  have hfactor : factorLengthBound m N b ≤ exp2 (3 * t + m + N) := by
    calc
      _ ≤ B * (exp2 N * (exp2 m * (B * B))) := by
        unfold factorLengthBound suffixNodeBound
        exact Nat.mul_le_mul (by omega)
          (Nat.mul_le_mul hN (hnode.trans (Nat.mul_le_mul_right _ hm)))
      _ = _ := by
        dsimp [B]
        rw [← exp2_add, ← exp2_add, ← exp2_add, ← exp2_add]
        congr 1; omega
  have hbig : B ≤ exp2 (3 * t + m + N) := exp2_mono (by omega)
  have he : suffixLengthBound m N [] b + b + 2 ≤
      exp2 (3 * t + m + N + 2) := by
    rw [exp2_add (3 * t + m + N) 2]
    have hsmall := hb.trans hbig
    change factorLengthBound m N b + 1 + b + 2 ≤ exp2 (3 * t + m + N) * 4
    omega
  apply he.trans (exp2_mono _)
  have hc : m + N + 5 ≤ exp2 (m + N + 10) :=
    (by omega : m + N + 5 ≤ m + N + 10).trans (le_exp2 _)
  have := Nat.mul_le_mul_right t hc
  nlinarith
private theorem iterate_log_bound (f : ℕ → ℕ) (C : ℕ)
    (hf : ∀ b t, b + 2 ≤ exp2 t → f b + b + 2 ≤ exp2 (C * t))
    (s b t : ℕ) (hb : b + 2 ≤ exp2 t) :
    (fun x => x + f x)^[s] b + 2 ≤ exp2 (C ^ s * t) := by
  induction s with
  | zero => simpa using hb
  | succ s ih =>
    rw [Function.iterate_succ_apply']
    have h := hf _ _ ih
    simpa only [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm,
      Nat.add_comm] using h
end DeciSigma1.Holes.Tail
end
end

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open Arithmetic
namespace DeciSigma1.Holes.Tail
theorem _root_.solution (m N S j b t : ℕ) (hb : b + 2 ≤ exp2 t) :
    suffixLengthBound m N (List.replicate j S) b + b + 2 ≤
      exp2 (exp2 ((m + N + 10) * (S + 3) ^ j) * t) := by
  induction j generalizing b t with
  | zero => simpa using base_log_bound m N b t hb
  | succ j ih =>
    let C := exp2 ((m + N + 10) * (S + 3) ^ j)
    let f := suffixLengthBound m N (List.replicate j S)
    let x := (fun x => x + f x)^[S] b
    have ht := exponent_pos hb
    have hC : 4 ≤ C := by
      have hp : 1 ≤ (S + 3) ^ j := Nat.one_le_pow _ _ (by omega)
      have : 2 ≤ (m + N + 10) * (S + 3) ^ j := by nlinarith
      exact exp2_mono this
    have hx : x + 2 ≤ exp2 (C ^ S * t) := iterate_log_bound f C ih S b t hb
    have hfx : f x + x + 2 ≤ exp2 (C ^ (S + 1) * t) := by
      have h := ih x _ hx
      change f x + x + 2 ≤ exp2 (C * (C ^ S * t)) at h
      simpa only [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
    have hy : (x + f x) + 2 ≤ exp2 (C ^ (S + 1) * t) := by omega
    have hfy : f (x + f x) + (x + f x) + 2 ≤ exp2 (C ^ (S + 2) * t) := by
      have h := ih (x + f x) _ hy
      change f (x + f x) + (x + f x) + 2 ≤ exp2 (C * (C ^ (S + 1) * t)) at h
      simpa only [show S + 2 = (S + 1) + 1 by omega, pow_succ,
        Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
    have hbx : b ≤ x := le_iterate_of_le_self (fun a => Nat.le_add_right a (f a)) S b
    have hpow : C ^ (S + 1) * t ≤ C ^ (S + 2) * t := by
      apply Nat.mul_le_mul_right
      exact Nat.pow_le_pow_right (by omega) (by omega)
    have hfx' := hfx.trans (exp2_mono hpow)
    have hsum : suffixLengthBound m N (List.replicate (j + 1) S) b + b + 2 ≤
        exp2 (C ^ (S + 2) * t + 2) := by
      rw [List.replicate_succ, suffixLengthBound_cons, exp2_add]
      change 2 * f x + f (x + f x) + 2 + b + 2 ≤
        exp2 (C ^ (S + 2) * t) * 4
      omega
    have hp : 1 ≤ C ^ (S + 2) := Nat.one_le_pow _ _ (by omega)
    have hnext : C ^ (S + 2) * t + 2 ≤ C ^ (S + 3) * t := by
      rw [show S + 3 = (S + 2) + 1 by omega, pow_succ C (S + 2)]
      have hprod := Nat.mul_le_mul hp ht
      have hmul := Nat.mul_le_mul_left (C ^ (S + 2) * t) hC
      nlinarith only [hprod, hmul]
    apply hsum.trans ((exp2_mono hnext).trans _)
    apply exp2_mono
    dsimp [C]
    rw [← exp2_mul, pow_succ]
    exact le_of_eq (congrArg (fun z => exp2 z * t) (by ring))
end DeciSigma1.Holes.Tail
