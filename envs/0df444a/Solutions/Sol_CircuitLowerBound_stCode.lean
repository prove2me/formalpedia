-- Prove2me | solution 1 for CircuitLowerBound.stCode
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T23:24:00.409094+00:00
-- url     : https://prove2.me/submissions/1769cd17-7a05-45b3-bf2b-7fe770a0fb53

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Interfaces
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Small
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_ofWord_toWord
set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork
open SmallFacts

namespace StCodeAux

theorem ones_append (j : ℕ) (x : List Bool) : ones (List.replicate j true ++ false :: x) = j := by
  induction j with
  | zero => simp [ones]
  | succ j ih =>
    simp only [ones, List.replicate_succ, List.cons_append, List.takeWhile_cons, id, if_true, List.length_cons] at ih ⊢
    rw [ih]

theorem rest_append (j : ℕ) (x : List Bool) : rest (List.replicate j true ++ false :: x) = x := by
  induction j with
  | zero => simp [rest]
  | succ j ih =>
    simp only [rest, List.replicate_succ, List.cons_append, List.dropWhile_cons, id, if_true] at ih ⊢
    exact ih

/-- A word that ends with 1 is the list of binary digits of a number. -/
theorem bits_foldr (w : List Bool) : Nat.bits ((w ++ [true]).foldr Nat.bit 0) = w ++ [true] := by
  induction w with
  | nil => simp [Nat.bit]
  | cons b w ih =>
    rw [List.cons_append, List.foldr_cons, Nat.bits_append_bit _ _ fun h => ?_, ih]
    rw [h] at ih
    simp at ih

theorem le_foldr (j : ℕ) (w : List Bool) : j ≤ (List.replicate j true ++ w).foldr Nat.bit 0 := by
  induction j with
  | zero => exact Nat.zero_le _
  | succ j ih =>
    rw [List.replicate_succ, List.cons_append, List.foldr_cons, Nat.bit_true_apply]
    omega

/-- The i-th number of W bits in a word that begins with numbers of W bits. -/
theorem fld_flatten (W : ℕ) (r : List Bool) : ∀ (X : List ℕ), (∀ x ∈ X, x < 2 ^ W) → ∀ i, i < X.length →
    fld W ((X.map (toWord W)).flatten ++ r) i = X.getD i 0
  | [], _, i, hi => by simp at hi
  | x :: X, h, 0, _ => by
    have : block W 0 (((x :: X).map (toWord W)).flatten ++ r) = toWord W x := by
      simp only [block, Nat.zero_mul, List.drop_zero, List.map_cons, List.flatten_cons, List.append_assoc]
      exact List.take_left' (length_toWord _ _)
    rw [fld, this, ofWord_toWord (h x (by simp))]
    rfl
  | x :: X, h, i + 1, hi => by
    have : block W (i + 1) (((x :: X).map (toWord W)).flatten ++ r) = block W i ((X.map (toWord W)).flatten ++ r) := by
      simp only [block, List.map_cons, List.flatten_cons, List.append_assoc]
      rw [Nat.add_mul, Nat.one_mul, Nat.add_comm, ← List.drop_drop, List.drop_left' (length_toWord _ _)]
    have ih := fld_flatten W r X (fun y hy => h y (by simp [hy])) i (by simpa using hi)
    rw [fld] at ih ⊢
    rw [this, ih]
    rfl

theorem length_n15 (c : TCl) : (n15 c).length = 15 := by simp [n15, n5]

/-- Entry 15·r + i of the numbers of a list of clauses. -/
theorem getD_flat15 : ∀ (X : List TCl) (r i : ℕ), r < X.length → i < 15 → ((X.map n15).flatten).getD (15 * r + i) 0 = (n15 (X.getD r zeroCl)).getD i 0
  | [], r, i, hr, _ => by simp at hr
  | c :: X, 0, i, _, hi => by
    rw [List.map_cons, List.flatten_cons, Nat.mul_zero, Nat.zero_add, List.getD_append _ _ _ _ (by rw [length_n15]; exact hi)]
    rfl
  | c :: X, r + 1, i, hr, hi => by
    rw [List.map_cons, List.flatten_cons, List.getD_append_right _ _ _ _ (by rw [length_n15]; omega), length_n15,
      show 15 * (r + 1) + i - 15 = 15 * r + i by omega, getD_flat15 X r i (by simpa using hr) hi]
    rfl

theorem length_flat15 (X : List TCl) : ((X.map n15).flatten).length = 15 * X.length := by
  induction X with
  | nil => rfl
  | cons c X ih => rw [List.map_cons, List.flatten_cons, List.length_append, ih, length_n15, List.length_cons]; ring

end StCodeAux

open StCodeAux

/-- Every table has arbitrarily large numbers. -/
theorem solution : StCode := by
  intro e a₀
  obtain ⟨k₀, l₀, X⟩ := e
  obtain ⟨nums, hnums⟩ : ∃ nums, nums = k₀ :: l₀ :: (X.map n15).flatten := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W, W = nums.sum + 1 := ⟨_, rfl⟩
  have hlt : ∀ x ∈ nums, x < 2 ^ W := fun x hx =>
    lt_of_le_of_lt (List.single_le_sum (by simp) x hx) (lt_trans (Nat.lt_succ_self _) (hW ▸ Nat.lt_two_pow_self))
  obtain ⟨v, hv⟩ : ∃ v, v = (nums.map (toWord W)).flatten ++ [true] := ⟨_, rfl⟩
  have hlen : nums.length = 2 + 15 * X.length := by rw [hnums, List.length_cons, List.length_cons, length_flat15]; omega
  have hvlen : v.length = nums.length * W + 1 := by
    rw [hv, List.length_append, List.length_flatten, List.map_map]
    have : (nums.map (List.length ∘ toWord W)) = List.replicate nums.length W := by
      rw [List.eq_replicate_iff]; simp [length_toWord]
    rw [this]; simp
  have hf : ∀ i, i < nums.length → fld W v i = nums.getD i 0 := fun i hi => by rw [hv]; exact fld_flatten W _ nums hlt i hi
  refine ⟨((List.replicate a₀ true ++ false :: (List.replicate W true ++ false :: (nums.map (toWord W)).flatten)) ++ [true]).foldr Nat.bit 0, ?_, ?_⟩
  · rw [List.append_assoc]; exact le_foldr _ _
  · rw [codeOf, bits_foldr, List.append_assoc, List.cons_append, rest_append, List.append_assoc, List.cons_append, ← hv, codeOfWord, ones_append, rest_append]
    have hR : (v.length - 2 * W) / (15 * W) = X.length := by
      rw [hvlen, hlen]
      have : (2 + 15 * X.length) * W + 1 - 2 * W = 15 * W * X.length + 1 := by
        have : (2 + 15 * X.length) * W = 2 * W + 15 * W * X.length := by ring
        omega
      rw [this, Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega), Nat.add_zero]
    have e0 : nums.getD 0 0 = k₀ := by rw [hnums]; rfl
    have e1 : nums.getD 1 0 = l₀ := by rw [hnums]; rfl
    rw [hR, hf 0 (by omega), hf 1 (by omega), e0, e1]
    have hlit : ∀ r < X.length, ∀ i, i + 5 ≤ 15 → ∀ l : TLit, (∀ f < 5, (n15 (X.getD r zeroCl)).getD (i + f) 0 = (n5 l).getD f 0) → litOf W v (2 + 15 * r + i) = l := by
      intro r hr i hi l hl
      have hg : ∀ f < 5, fld W v (2 + 15 * r + i + f) = (n5 l).getD f 0 := by
        intro f hf5
        rw [hf _ (by omega), hnums, show 2 + 15 * r + i + f = (15 * r + (i + f)) + 1 + 1 by omega, List.getD_cons_succ, List.getD_cons_succ,
          getD_flat15 X r (i + f) hr (by omega), hl f hf5]
      have g0 := hg 0 (by omega)
      have g1 := hg 1 (by omega)
      have g2 := hg 2 (by omega)
      have g3 := hg 3 (by omega)
      have g4 := hg 4 (by omega)
      simp only [Nat.add_zero] at g0
      rw [litOf, g0, g1, g2, g3, g4]
      obtain ⟨x1, x2, x3, x4, x5⟩ := l
      cases x5 <;> simp [n5]
    refine congrArg (fun z => (k₀, l₀, z)) ?_
    apply List.ext_getElem
    · simp
    · intro r h1 h2
      have hr : r < X.length := h2
      simp only [List.getElem_map, List.getElem_range]
      have hc : X.getD r zeroCl = X[r] := List.getD_eq_getElem _ _ hr
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · exact hlit r hr 0 (by omega) _ fun f hf5 => by rw [hc]; interval_cases f <;> rfl
      · exact hlit r hr 5 (by omega) _ fun f hf5 => by rw [hc]; interval_cases f <;> rfl
      · exact hlit r hr 10 (by omega) _ fun f hf5 => by rw [hc]; interval_cases f <;> rfl
