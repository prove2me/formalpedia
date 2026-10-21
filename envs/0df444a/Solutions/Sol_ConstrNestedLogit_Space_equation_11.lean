-- Prove2me | solution 1 for ConstrNestedLogit.Space.equation_11
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-20T18:41:46.341997+00:00
-- url     : https://prove2.me/submissions/91b51112-1f28-4311-8957-8caf7f8bac37

import Mathlib
import Definitions.Def_ConstrNestedLogit_Space_Model

open scoped BigOperators
open ConstrNestedLogit.Space

namespace KnapsackRounding

lemma support_nonneg {n : ℕ} (w a x : Fin n → ℝ) (c : ℝ)
    (hw : ∀ k, 0 ≤ w k) (hx : knapsackLPOptimal w a c x)
    (k : Fin n) (hk : 0 < x k) : 0 ≤ a k := by
  classical
  by_contra ha
  have ha : a k < 0 := lt_of_not_ge ha
  let y : Fin n → ℝ := fun l => if l = k then 0 else x l
  have hy : knapsackLPFeasible w c y := by
    constructor
    · intro l
      by_cases hl : l = k
      · simp [y, hl]
      · simpa [y, hl] using hx.1.1 l
    · apply le_trans _ hx.1.2
      apply Finset.sum_le_sum
      intro l hl
      by_cases hlk : l = k
      · subst l
        simpa [y] using mul_nonneg (hw k) (hx.1.1 k).1
      · simp [y, hlk]
  have hs : knapsackLPObjective a x < knapsackLPObjective a y := by
    apply Finset.sum_lt_sum
    · intro l hl
      by_cases hlk : l = k
      · subst l
        simp only [y, if_pos rfl, mul_zero]
        exact le_of_lt (mul_neg_of_neg_of_pos ha hk)
      · simp [y, hlk]
    · exact ⟨k, Finset.mem_univ k, by simpa [y] using mul_neg_of_neg_of_pos ha hk⟩
  exact (not_lt_of_ge (hx.2 y hy)) hs

lemma objective_split {n : ℕ} (a x : Fin n → ℝ)
    (hx : ∀ k, 0 ≤ x k ∧ x k ≤ 1) (j : Option (Fin n))
    (hj : ∀ k, (0 < x k ∧ x k < 1) ↔ j = some k) :
    knapsackLPObjective a x =
      (∑ k ∈ rounded x, a k) +
        (match j with | none => 0 | some k => a k * x k) := by
  classical
  have hbin (k : Fin n) (hk : j ≠ some k) : x k = 0 ∨ x k = 1 := by
    by_contra h
    have h0 : x k ≠ 0 := fun h0 => h (Or.inl h0)
    have h1 : x k ≠ 1 := fun h1 => h (Or.inr h1)
    exact hk ((hj k).mp ⟨lt_of_le_of_ne (hx k).1 (Ne.symm h0),
      lt_of_le_of_ne (hx k).2 h1⟩)
  cases j with
  | none =>
    simp only [add_zero, knapsackLPObjective, rounded, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k hk
    rcases hbin k (by simp) with h | h <;> simp [h]
  | some k =>
    have hk := (hj k).mpr rfl
    have heq (l : Fin n) :
        a l * x l = (if x l = 1 then a l else 0) +
          (if l = k then a k * x k else 0) := by
      by_cases hl : l = k
      · subst l
        simp [ne_of_lt hk.2]
      · rcases hbin l (by simpa using Ne.symm hl) with h | h <;> simp [h, hl]
    simp only [knapsackLPObjective, rounded, Finset.sum_filter]
    calc
      _ = ∑ l, ((if x l = 1 then a l else 0) +
          (if l = k then a k * x k else 0)) := Finset.sum_congr rfl (fun l _ => heq l)
      _ = _ := by rw [Finset.sum_add_distrib]; simp

lemma integer_le_lp {n : ℕ} (w a x : Fin n → ℝ) (c : ℝ)
    (hx : knapsackLPOptimal w a c x)
    (T : Finset (Fin n)) (hT : ∑ k ∈ T, w k ≤ c) :
    (∑ k ∈ T, a k) ≤ knapsackLPObjective a x := by
  classical
  let y : Fin n → ℝ := fun k => if k ∈ T then 1 else 0
  have hy : knapsackLPFeasible w c y := by
    constructor
    · intro k
      by_cases hk : k ∈ T <;> simp [y, hk]
    · simpa [y, mul_ite] using hT
  simpa [knapsackLPObjective, y, mul_ite] using hx.2 y hy

end KnapsackRounding

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (I : NestedLogitVariants.LP.Instance ι n)
    (w : ι → Fin n → ℝ) (c : ι → ℝ) (i : ι)
    (hvnp : ∀ i, I.vnp i = 0) (hv : ∀ j, 0 < I.v i j)
    (hw : ∀ j, 0 < w i j) (hwc : ∀ j, w i j ≤ c i)
    (u : ℝ) (hu : 0 ≤ u) (x : Fin n → ℝ)
    (hx : spaceLPOptimal I w c i u x) (j : Option (Fin n))
    (hj : ∀ k, (0 < x k ∧ x k < 1) ↔ j = some k) :
    ∀ T : Finset (Fin n), spaceFeasible w c i T →
      assortmentUtility I i u T ≤
        2 * max (assortmentUtility I i u (rounded x))
          (match j with | none => 0 | some k => utility I i u k) := by
  intro T hT
  have hbound := KnapsackRounding.integer_le_lp (w i) (utility I i u) x (c i) hx T hT
  have hsplit := KnapsackRounding.objective_split (utility I i u) x hx.1.1 j hj
  change assortmentUtility I i u T ≤ _ at hbound
  change knapsackLPObjective (utility I i u) x =
    assortmentUtility I i u (rounded x) + _ at hsplit
  cases j with
  | none =>
    simp only [add_zero] at hsplit
    have hmax := le_max_left (assortmentUtility I i u (rounded x)) (0 : ℝ)
    have hnonneg := le_max_right (assortmentUtility I i u (rounded x)) (0 : ℝ)
    dsimp
    linarith
  | some k =>
    have hk := (hj k).mpr rfl
    have ha := KnapsackRounding.support_nonneg (w i) (utility I i u) x (c i)
      (fun l => (hw l).le) hx k hk.1
    have hprod : utility I i u k * x k ≤ utility I i u k :=
      mul_le_of_le_one_right ha (hx.1.1 k).2
    have hmax₁ := le_max_left (assortmentUtility I i u (rounded x)) (utility I i u k)
    have hmax₂ := le_max_right (assortmentUtility I i u (rounded x)) (utility I i u k)
    dsimp at hsplit ⊢
    linarith

#print axioms solution
