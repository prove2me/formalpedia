-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.freshTupleBound_le_double_exp2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:07:19.554216+00:00
-- url     : https://prove2.me/submissions/5ece063e-1343-486b-a296-2e12793c8d47

module
public import Mathlib.Tactic.Positivity.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_ElementaryBounds
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Bound
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ElementaryBound
public import Theorems.Thm_DeciSigma1_Arithmetic_exp2_add
public import Theorems.Thm_DeciSigma1_Arithmetic_exp2_add_le
public import Theorems.Thm_DeciSigma1_Arithmetic_exp2_mono
public import Theorems.Thm_DeciSigma1_Arithmetic_exp2_mul
public import Theorems.Thm_DeciSigma1_Arithmetic_le_exp2
public import Theorems.Thm_DeciSigma1_Arithmetic_quadratic_step_le_exp2
public import Theorems.Thm_DeciSigma1_Arithmetic_succ_le_exp2
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Fresh_length_reversedBlocks
public import Theorems.Thm_DeciSigma1_Holes_Fresh_length_upperSeq
public import Theorems.Thm_DeciSigma1_Holes_Fresh_marker_zero
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_one
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_zero
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans
public import Theorems.Thm_DeciSigma1_Words_deletePositions_empty
public import Theorems.Thm_DeciSigma1_Words_deletePositions_nil
public import Theorems.Thm_DeciSigma1_Words_greatestPreimage_empty
public import Theorems.Thm_DeciSigma1_Words_retainedCount_empty
public import Theorems.Thm_DeciSigma1_Words_retainedCount_greatestPreimage
public import Theorems.Thm_DeciSigma1_Words_retainedCount_zero
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.Holes.Fresh.length_reversedBlocks
attribute [local simp] DeciSigma1.Holes.Fresh.length_upperSeq
attribute [local simp] DeciSigma1.Holes.Fresh.marker_zero
attribute [local simp] DeciSigma1.Holes.Fresh.mem_active_one
attribute [local simp] DeciSigma1.Holes.Fresh.mem_active_zero
attribute [local simp] DeciSigma1.Words.deletePositions_empty
attribute [local simp] DeciSigma1.Words.deletePositions_nil
attribute [local simp] DeciSigma1.Words.greatestPreimage_empty
attribute [local simp] DeciSigma1.Words.retainedCount_empty
attribute [local simp] DeciSigma1.Words.retainedCount_greatestPreimage
attribute [local simp] DeciSigma1.Words.retainedCount_zero
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc


section
@[expose] public section
namespace DeciSigma1.Holes.Fresh
open Arithmetic
private theorem edgeLengthBound_le_exp2 (k n : ℕ) :
    edgeLengthBound k n ≤ exp2 (arithmeticBudget k n) := by
  have hm : deletionMargin k n ≤ 3 * k * n + 5 := by
    have h := Nat.mul_le_mul_left k (Nat.sub_le n 1)
    unfold deletionMargin
    nlinarith
  have hp : (k + 1) ^ (k * n + 1) * n ^ n ≤
      exp2 (k * (k * n + 1) + n * n) := by
    rw [exp2_add, exp2_mul, exp2_mul]
    exact Nat.mul_le_mul (Nat.pow_le_pow_left (succ_le_exp2 k) _)
      (Nat.pow_le_pow_left (le_exp2 n) _)
  calc
    edgeLengthBound k n ≤ exp2 (k * (k * n + 1) + n * n) +
        exp2 (6 * k * n + 11) := by
      unfold edgeLengthBound
      have := le_exp2 (6 * k * n + 11)
      nlinarith
    _ ≤ exp2 (k * (k * n + 1) + n * n + (6 * k * n + 11) + 1) :=
      exp2_add_le _ _
    _ ≤ _ := exp2_mono (by unfold arithmeticBudget; nlinarith)
private theorem parseFactor_le_exp2 (k n : ℕ) :
    parseFactor k n ≤ exp2 (arithmeticBudget k n) := by
  apply exp2_mono
  have := Nat.mul_le_mul_left k (Nat.sub_le n 1)
  have hkn : k * n ≤ 7 * k * n := by nlinarith
  unfold arithmeticBudget
  omega
private theorem textCountBoundAtDepth_le_exp2 (k n d : ℕ) :
    textCountBoundAtDepth k n d ≤ exp2 ((4 * arithmeticBudget k n + 4) * 3 ^ d) := by
  induction d with
  | zero =>
    simp only [textCountBoundAtDepth, pow_zero, Nat.mul_one]
    exact (succ_le_exp2 k).trans (exp2_mono (by unfold arithmeticBudget; omega))
  | succ d ih =>
    refine (quadratic_step_le_exp2 ih (parseFactor_le_exp2 k n)
      (edgeLengthBound_le_exp2 k n)).trans (exp2_mono ?_)
    have h := Nat.one_le_pow d 3 (by decide)
    rw [pow_succ]
    nlinarith
end DeciSigma1.Holes.Fresh
end
end

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open Arithmetic
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution (k n : ℕ) :
    freshTupleBound k n ≤ exp2 (exp2 ((k + n + 16) ^ 4)) := by
  let q := arithmeticBudget k n
  let B := 4 * q + 4
  let d := k * n
  have ht : textCountBound k n ≤ exp2 (B * 3 ^ d) :=
    textCountBoundAtDepth_le_exp2 k n d
  have ha := parseFactor_le_exp2 k n
  have he := edgeLengthBound_le_exp2 k n
  have hp : textCountBound k n * parseFactor k n ≤ exp2 (B * 3 ^ d + q) := by
    rw [exp2_add]; exact Nat.mul_le_mul ht ha
  have hx : expansionBlockCountBound k n ≤ exp2 (B * 3 ^ d + 2 * q + 2) := by
    calc
      _ ≤ exp2 (B * 3 ^ d + q + 2) * exp2 q :=
        Nat.mul_le_mul ((Nat.add_le_add hp (le_refl 2)).trans
          (exp2_add_le (B * 3 ^ d + q) 1)) he
      _ = _ := by rw [← exp2_add]; congr 1; omega
  have hB : B ≤ B * 3 ^ d := Nat.le_mul_of_pos_right _ (by positivity)
  have hx' : expansionBlockCountBound k n ≤ exp2 (2 * B * 3 ^ d) :=
    hx.trans (exp2_mono (by dsimp [B] at *; nlinarith))
  have hthree : 3 ^ d ≤ exp2 (2 * d) := by
    rw [exp2_mul]
    exact Nat.pow_le_pow_left (by decide : 3 ≤ exp2 2) d
  have hlog : 2 * B * 3 ^ d * (d + 1) ≤ exp2 (B + 3 * d + 1) := by
    calc
      _ ≤ 2 * exp2 B * exp2 (2 * d) * exp2 d :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left 2 (le_exp2 B)) hthree)
          (succ_le_exp2 d)
      _ = _ := by
        change exp2 1 * exp2 B * exp2 (2 * d) * exp2 d = _
        rw [← exp2_add, ← exp2_add, ← exp2_add]
        congr 1; omega
  have hpoly : k + B + 3 * d + 2 ≤ (k + n + 16) ^ 4 := by
    dsimp [B, q, d, arithmeticBudget]
    ring_nf
    omega
  calc
    freshTupleBound k n ≤ exp2 k * exp2 (2 * B * 3 ^ d) ^ (d + 1) :=
      Nat.mul_le_mul (le_exp2 k) (Nat.pow_le_pow_left hx' _)
    _ = exp2 (k + 2 * B * 3 ^ d * (d + 1)) := by rw [← exp2_mul, ← exp2_add]
    _ ≤ exp2 (exp2 k + exp2 (B + 3 * d + 1)) :=
      exp2_mono (Nat.add_le_add (le_exp2 k) hlog)
    _ ≤ exp2 (exp2 (k + (B + 3 * d + 1) + 1)) := exp2_mono (exp2_add_le _ _)
    _ ≤ exp2 (exp2 ((k + n + 16) ^ 4)) :=
      exp2_mono (exp2_mono (by omega))
end DeciSigma1.Holes.Fresh
