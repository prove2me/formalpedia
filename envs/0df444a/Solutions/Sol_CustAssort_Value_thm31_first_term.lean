-- Prove2me | solution 1 for CustAssort.Value.thm31_first_term
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:49:53.923546+00:00
-- url     : https://prove2.me/submissions/ed1d72df-c755-48e9-b749-e4613232359e

import Mathlib
import Definitions.Def_CustAssort_Value_Setting

set_option autoImplicit false
open CustAssort.Value

theorem W_geo (a : ℝ) (ha : 2 ≤ a) (n : ℕ) :
    ∑ i ∈ Finset.range n, a ^ (i + 1) ≤ 2 * a ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h1 : 2 * a ^ n ≤ a ^ (n + 1) := by
      rw [pow_succ]
      have : 0 ≤ a ^ n := by positivity
      nlinarith
    have h2 : 2 * a ^ (n + 1) = 2 * a ^ (n + 1) := rfl
    have : a ^ (n + 1) ≤ a ^ (n + 1) := le_refl _
    nlinarith [pow_pos (by linarith : (0 : ℝ) < a) (n + 1)]

theorem solution (m : ℕ) (a b : ℝ) (ha : 2 ≤ a) (hb : 1 ≤ b)
    (S : Finset (Fin m)) (j : Fin m) :
    firstTerm a b S j ≤ 2 * alpha a m * b ^ m / a := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hα : 0 ≤ alpha a m := by
    unfold alpha
    apply inv_nonneg.mpr
    exact Finset.sum_nonneg (fun i _ => by positivity)
  have hθ : 0 ≤ thetaI a m j := by
    unfold thetaI; positivity
  have hvnn : ∀ i : Fin m, 0 ≤ vI b m i j := by
    intro i; unfold vI; split_ifs <;> positivity
  have hD : 1 ≤ 1 + ∑ i ∈ S, vI b m i j := by
    have : 0 ≤ ∑ i ∈ S, vI b m i j := Finset.sum_nonneg (fun i _ => hvnn i)
    linarith
  -- numerator bound
  have hterm : ∀ i : Fin m, (if i < j then revI a m i * b ^ (m - i.val) else 0) ≤
      (if i.val < j.val then a ^ (i.val + 1) * b ^ m else 0) := by
    intro i
    by_cases h : i < j
    · have h' : i.val < j.val := h
      simp only [h, h', if_true]
      unfold revI
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact pow_le_pow_right₀ hb (Nat.sub_le _ _)
    · have h' : ¬ i.val < j.val := h
      simp [h, h']
  have hnum : (∑ i ∈ S, if i < j then revI a m i * b ^ (m - i.val) else 0) ≤
      2 * a ^ j.val * b ^ m := by
    calc (∑ i ∈ S, if i < j then revI a m i * b ^ (m - i.val) else 0)
        ≤ ∑ i ∈ S, (if i.val < j.val then a ^ (i.val + 1) * b ^ m else 0) :=
          Finset.sum_le_sum (fun i _ => hterm i)
      _ ≤ ∑ i : Fin m, (if i.val < j.val then a ^ (i.val + 1) * b ^ m else 0) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun i _ _ => by split_ifs <;> positivity)
      _ = ∑ i ∈ Finset.range m, (if i < j.val then a ^ (i + 1) * b ^ m else 0) :=
          Fin.sum_univ_eq_sum_range (fun i => if i < j.val then a ^ (i + 1) * b ^ m else 0) m
      _ = ∑ i ∈ Finset.range j.val, a ^ (i + 1) * b ^ m := by
          rw [← Finset.sum_filter]
          apply Finset.sum_congr _ (fun _ _ => rfl)
          ext i
          simp only [Finset.mem_filter, Finset.mem_range]
          constructor
          · rintro ⟨_, h⟩; exact h
          · intro h; exact ⟨lt_trans h j.isLt, h⟩
      _ = (∑ i ∈ Finset.range j.val, a ^ (i + 1)) * b ^ m := by rw [Finset.sum_mul]
      _ ≤ 2 * a ^ j.val * b ^ m :=
          mul_le_mul_of_nonneg_right (W_geo a ha j.val) (by positivity)
  unfold firstTerm
  have hnn : 0 ≤ ∑ i ∈ S, (if i < j then revI a m i * b ^ (m - i.val) else 0) :=
    Finset.sum_nonneg (fun i _ => by split_ifs <;> [exact (by unfold revI; positivity); exact le_refl _])
  calc thetaI a m j * (∑ i ∈ S, if i < j then revI a m i * b ^ (m - i.val) else 0) /
        (1 + ∑ i ∈ S, vI b m i j)
      ≤ thetaI a m j * (∑ i ∈ S, if i < j then revI a m i * b ^ (m - i.val) else 0) / 1 :=
        div_le_div_of_nonneg_left (by positivity) one_pos hD
    _ ≤ thetaI a m j * (2 * a ^ j.val * b ^ m) := by
        rw [div_one]; exact mul_le_mul_of_nonneg_left hnum hθ
    _ = 2 * alpha a m * b ^ m / a := by
        unfold thetaI
        have : a ^ (j.val + 1) ≠ 0 := by positivity
        have : a ^ j.val ≠ 0 := by positivity
        field_simp
        ring

