-- Prove2me | solution 1 for GTWSched.FixedOrder.shift_cost_eq
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T04:15:22.464199+00:00
-- url     : https://prove2.me/submissions/9d4bf4f4-bd7c-44b8-90d4-29d98ed7b8bb

import Mathlib
import Definitions.Def_GTWSched_FixedOrder_Algorithm



namespace GTWSched.FixedOrder

lemma foldl_min_aux (a s : ℕ → ℝ) (L : List ℕ) (d : ℝ) :
    L.foldl (fun d i => if a i < s i then min d (s i - a i) else d) d ≤ d ∧
    (∀ i ∈ L, a i < s i →
      L.foldl (fun d i => if a i < s i then min d (s i - a i) else d) d ≤ s i - a i) ∧
    (L.foldl (fun d i => if a i < s i then min d (s i - a i) else d) d = d ∨
      ∃ i ∈ L, a i < s i ∧
        L.foldl (fun d i => if a i < s i then min d (s i - a i) else d) d = s i - a i) := by
  induction L generalizing d with
  | nil => simp
  | cons x L ih =>
    simp only [List.foldl_cons]
    by_cases hx : a x < s x
    · simp only [hx, if_true]
      obtain ⟨h1, h2, h3⟩ := ih (min d (s x - a x))
      refine ⟨h1.trans (min_le_left _ _), ?_, ?_⟩
      · intro i hi hai
        rcases List.mem_cons.mp hi with rfl | hi
        · exact h1.trans (min_le_right _ _)
        · exact h2 i hi hai
      · rcases h3 with h3 | ⟨i, hi, hai, h3⟩
        · rcases min_choice d (s x - a x) with h | h
          · left; rw [h3, h]
          · right; exact ⟨x, List.mem_cons_self, hx, by rw [h3, h]⟩
        · right; exact ⟨i, List.mem_cons_of_mem _ hi, hai, h3⟩
    · simp only [hx, if_false]
      obtain ⟨h1, h2, h3⟩ := ih d
      refine ⟨h1, ?_, ?_⟩
      · intro i hi hai
        rcases List.mem_cons.mp hi with rfl | hi
        · exact absurd hai hx
        · exact h2 i hi hai
      · rcases h3 with h3 | ⟨i, hi, hai, h3⟩
        · left; exact h3
        · right; exact ⟨i, List.mem_cons_of_mem _ hi, hai, h3⟩

lemma foldl_ge_aux (a s : ℕ → ℝ) (L : List ℕ) (d c : ℝ) (hd : c ≤ d)
    (h : ∀ i ∈ L, a i < s i → c ≤ s i - a i) :
    c ≤ L.foldl (fun d i => if a i < s i then min d (s i - a i) else d) d := by
  induction L generalizing d with
  | nil => simpa using hd
  | cons x L ih =>
    simp only [List.foldl_cons]
    apply ih
    · by_cases hx : a x < s x
      · simp only [hx, if_true]
        exact le_min hd (h x List.mem_cons_self hx)
      · simp only [hx, if_false]; exact hd
    · intro i hi; exact h i (List.mem_cons_of_mem _ hi)

lemma shiftAmount_le (a l s : ℕ → ℝ) (j m : ℕ) :
    shiftAmount a l s j m ≤ s j - prevEnd l s j ∧
    (∀ i, j ≤ i → i ≤ m → a i < s i → shiftAmount a l s j m ≤ s i - a i) := by
  obtain ⟨h1, h2, -⟩ := foldl_min_aux a s (Finset.Icc j m).toList (s j - prevEnd l s j)
  refine ⟨h1, fun i hji him hai => h2 i ?_ hai⟩
  simp [Finset.mem_Icc, hji, him]

lemma shiftAmount_cases (a l s : ℕ → ℝ) (j m : ℕ) :
    shiftAmount a l s j m = s j - prevEnd l s j ∨
    ∃ i, j ≤ i ∧ i ≤ m ∧ a i < s i ∧ shiftAmount a l s j m = s i - a i := by
  obtain ⟨-, -, h3⟩ := foldl_min_aux a s (Finset.Icc j m).toList (s j - prevEnd l s j)
  rcases h3 with h | ⟨i, hi, hai, h⟩
  · left; exact h
  · right
    simp only [Finset.mem_toList, Finset.mem_Icc] at hi
    exact ⟨i, hi.1, hi.2, hai, h⟩

lemma shiftAmount_ge (a l s : ℕ → ℝ) (j m : ℕ) (c : ℝ) (h1 : c ≤ s j - prevEnd l s j)
    (h2 : ∀ i, j ≤ i → i ≤ m → a i < s i → c ≤ s i - a i) :
    c ≤ shiftAmount a l s j m := by
  apply foldl_ge_aux a s _ _ c h1
  intro i hi hai
  simp only [Finset.mem_toList, Finset.mem_Icc] at hi
  exact h2 i hi.1 hi.2 hai

lemma shift_cost_core (a l s : ℕ → ℝ) (m j : ℕ) (δ : ℝ)
    (hbalance : decCount a s j m = incCount a s j m)
    (hδ : 0 ≤ δ ∧ δ ≤ shiftAmount a l s j m) :
    cost a (m + 1) (shiftRange s j m δ) = cost a (m + 1) s := by
  obtain ⟨h0, h1⟩ := hδ
  have hle := (shiftAmount_le a l s j m).2
  unfold cost
  have key : ∀ i ∈ Finset.range (m+1), |shiftRange s j m δ i - a i| =
      |s i - a i| + (if j ≤ i ∧ i ≤ m then (if a i < s i then -δ else δ) else 0) := by
    intro i hi
    by_cases hij : j ≤ i ∧ i ≤ m
    · simp only [shiftRange, hij, and_self, if_true]
      by_cases hai : a i < s i
      · have := hle i hij.1 hij.2 hai
        simp only [hai, if_true]
        rw [abs_of_nonneg (by linarith), abs_of_pos (by linarith)]; ring
      · have hai' : s i ≤ a i := not_lt.mp hai
        simp only [hai, if_false]
        rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; ring
    · simp [shiftRange, hij]
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib]
  have : ∑ i ∈ Finset.range (m+1), (if j ≤ i ∧ i ≤ m then (if a i < s i then -δ else δ) else (0:ℝ)) = 0 := by
    rw [← Finset.sum_filter]
    have hf : (Finset.range (m+1)).filter (fun i => j ≤ i ∧ i ≤ m) = Finset.Icc j m := by
      ext i; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]; omega
    rw [hf, Finset.sum_ite, Finset.sum_const, Finset.sum_const]
    have : (Finset.Icc j m).filter (fun i => ¬ a i < s i) = (Finset.Icc j m).filter (fun i => s i ≤ a i) := by
      ext i; simp
    rw [this]
    unfold decCount incCount at hbalance
    rw [hbalance]; simp
  rw [this, add_zero]

theorem shift_cost_eq_core (a l s : ℕ → ℝ) (m j : ℕ) (δ : ℝ)
    (hfeas : FixedFeasible l (m + 1) s)
    (hblock : IsBlock l (m + 1) s j m)
    (hbalance : decCount a s j m = incCount a s j m)
    (hpositive : s j ≠ 0)
    (hδ : 0 ≤ δ ∧ δ ≤ shiftAmount a l s j m) :
    cost a (m + 1) (shiftRange s j m δ) = cost a (m + 1) s :=
  shift_cost_core a l s m j δ hbalance hδ

end GTWSched.FixedOrder

open GTWSched.FixedOrder


theorem solution (a l s : ℕ → ℝ) (m j : ℕ) (δ : ℝ)
    (hfeas : FixedFeasible l (m + 1) s)
    (hblock : IsBlock l (m + 1) s j m)
    (hbalance : decCount a s j m = incCount a s j m)
    (hpositive : s j ≠ 0)
    (hδ : 0 ≤ δ ∧ δ ≤ shiftAmount a l s j m) :
    cost a (m + 1) (shiftRange s j m δ) = cost a (m + 1) s := by
  exact shift_cost_eq_core a l s m j δ hfeas hblock hbalance hpositive hδ
