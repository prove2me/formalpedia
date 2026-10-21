-- Prove2me | solution 1 for ConstrNestedLogit.Space.refined_chain
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-20T18:44:42.706317+00:00
-- url     : https://prove2.me/submissions/561aac4f-647d-49c3-ae50-48981df32c86

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

theorem checked_equation11 {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
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

#print axioms checked_equation11

namespace KnapsackRounding

lemma fractional_ratio_bound {n : ℕ} (w a x : Fin n → ℝ) (c : ℝ)
    (hx : knapsackLPOptimal w a c x) (j : Fin n)
    (hw : 0 < w j) (hwc : w j ≤ c) (hj : x j < 1) :
    c * a j ≤ w j * knapsackLPObjective a x := by
  classical
  have hc : 0 < c := lt_of_lt_of_le hw hwc
  let q := c / w j
  have hq : 0 < q := div_pos hc hw
  let t := min 1 ((1 - x j) / q)
  have ht : 0 < t := lt_min (by norm_num) (div_pos (by linarith) hq)
  have ht1 : t ≤ 1 := min_le_left _ _
  have htq : t * q ≤ 1 - x j := (le_div_iff₀ hq).mp (min_le_right _ _)
  let y : Fin n → ℝ := fun k => (1-t) * x k + if k = j then t*q else 0
  have hy : knapsackLPFeasible w c y := by
    constructor
    · intro k
      have hbase : 0 ≤ (1-t) * x k := mul_nonneg (by linarith) (hx.1.1 k).1
      have hbasele : (1-t) * x k ≤ x k := by
        nlinarith [mul_nonneg ht.le (hx.1.1 k).1]
      by_cases hk : k = j
      · subst k
        dsimp [y]
        simp only [if_true]
        constructor
        · positivity
        · linarith
      · simp only [y, if_neg hk, add_zero]
        exact ⟨hbase, hbasele.trans (hx.1.1 k).2⟩
    · have heq : (∑ k, w k * y k) = (1-t) * (∑ k, w k * x k) + t*c := by
        simp only [y, mul_add, mul_ite, mul_zero, Finset.sum_add_distrib]
        simp only [show ∀ k, w k * ((1-t)*x k) = (1-t)*(w k*x k) by intro k; ring]
        rw [← Finset.mul_sum]
        simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
        dsimp [q]
        field_simp [ne_of_gt hw]
        <;> ring
      rw [heq]
      have hle := mul_le_mul_of_nonneg_left hx.1.2 (sub_nonneg.mpr ht1)
      nlinarith
  have heq : knapsackLPObjective a y =
      (1-t) * knapsackLPObjective a x + t*(q*a j) := by
    simp only [knapsackLPObjective, y, mul_add, mul_ite, mul_zero,
      Finset.sum_add_distrib]
    simp only [show ∀ k, a k * ((1-t)*x k) = (1-t)*(a k*x k) by intro k; ring]
    rw [← Finset.mul_sum]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  have hop := hx.2 y hy
  rw [heq] at hop
  have hratio : q * a j ≤ knapsackLPObjective a x := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hratio hw.le
  have heqq : w j * q = c := by dsimp [q]; field_simp [ne_of_gt hw]
  simpa only [← mul_assoc, heqq] using hmul

lemma objective_nonneg {n : ℕ} (w a x : Fin n → ℝ) (c : ℝ)
    (hx : knapsackLPOptimal w a c x) (hc : 0 ≤ c) :
    0 ≤ knapsackLPObjective a x := by
  have hzero : knapsackLPFeasible w c (fun _ => 0) := by
    exact ⟨fun _ => by norm_num, by simpa using hc⟩
  simpa [knapsackLPObjective] using hx.2 _ hzero

end KnapsackRounding

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (I : NestedLogitVariants.LP.Instance ι n)
    (w : ι → Fin n → ℝ) (c : ι → ℝ) (i : ι)
    (hvnp : ∀ i, I.vnp i = 0) (hv : ∀ k, 0 < I.v i k)
    (hw : ∀ k, 0 < w i k) (hwc : ∀ k, w i k ≤ c i)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hsmall : ∀ k, w i k ≤ ε * c i)
    (u : ℝ) (hu : 0 ≤ u) (x : Fin n → ℝ)
    (hx : spaceLPOptimal I w c i u x) (j : Fin n)
    (hj : oneFractional x j) :
    ∀ T : Finset (Fin n), spaceFeasible w c i T →
      assortmentUtility I i u T ≤
        (1 / (1 - ε)) * assortmentUtility I i u (rounded x) := by
  intro T hT
  have hc : 0 < c i := lt_of_lt_of_le (hw j) (hwc j)
  have hop := KnapsackRounding.objective_nonneg (w i) (utility I i u) x (c i) hx hc.le
  have ha := KnapsackRounding.support_nonneg (w i) (utility I i u) x (c i)
    (fun k => (hw k).le) hx j hj.1
  have hr := KnapsackRounding.fractional_ratio_bound (w i) (utility I i u) x (c i)
    hx j (hw j) (hwc j) hj.2.1
  have hs := mul_le_mul_of_nonneg_right (hsmall j) hop
  have hjbound : utility I i u j ≤ ε * knapsackLPObjective (utility I i u) x := by
    nlinarith
  have hloss : utility I i u j * x j ≤ ε * knapsackLPObjective (utility I i u) x :=
    (mul_le_of_le_one_right ha (hx.1.1 j).2).trans hjbound
  have hoption : ∀ k, (0 < x k ∧ x k < 1) ↔ some j = some k := by
    intro k
    constructor
    · intro hk
      by_contra hne
      have hkj : k ≠ j := by simpa [eq_comm] using hne
      rcases hj.2.2 k hkj with h | h <;> linarith [hk.1, hk.2]
    · intro hk
      have hkj : j = k := Option.some.inj hk
      subst k
      exact ⟨hj.1, hj.2.1⟩
  have hsplit := KnapsackRounding.objective_split (utility I i u) x hx.1.1 (some j) hoption
  change knapsackLPObjective (utility I i u) x =
    assortmentUtility I i u (rounded x) + utility I i u j * x j at hsplit
  have hmain : knapsackLPObjective (utility I i u) x * (1-ε) ≤
      assortmentUtility I i u (rounded x) := by nlinarith
  have hfrac := (le_div_iff₀ (show 0 < 1-ε by linarith)).mpr hmain
  have hb := KnapsackRounding.integer_le_lp (w i) (utility I i u) x (c i) hx T hT
  change assortmentUtility I i u T ≤ _ at hb
  simpa [div_eq_mul_inv, mul_comm] using hb.trans hfrac

#print axioms solution
