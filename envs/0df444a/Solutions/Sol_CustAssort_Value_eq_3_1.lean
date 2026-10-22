-- Prove2me | solution 1 for CustAssort.Value.eq_3_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:46:48.66338+00:00
-- url     : https://prove2.me/submissions/ef22adfe-3a8d-4b86-9d73-dbdfe5e50615

import Mathlib
import Definitions.Def_CustAssort_Value_Setting

set_option autoImplicit false
open CustAssort.Value

theorem solution (m : ℕ) (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (S : Finset (Fin m)) (j : Fin m) :
    thetaI a m j * CustAssort.AugGreedy.rev (vI b m) (revI a m) j S =
      firstTerm a b S j + secondTerm a b S j := by
  have hsplit : ∀ i : Fin m, revI a m i * vI b m i j =
      (if i < j then revI a m i * b ^ (m - i.val) else 0) +
        (if i = j then revI a m j * b ^ (m - j.val) else 0) := by
    intro i
    unfold vI
    by_cases h1 : i < j
    · have h2 : i ≤ j := h1.le
      have h3 : i ≠ j := h1.ne
      simp [h1, h2, h3]
    · by_cases h3 : i = j
      · subst h3; simp
      · have h2 : ¬ i ≤ j := fun h => h1 (lt_of_le_of_ne h h3)
        simp [h1, h2, h3]
  have hN : ∑ i ∈ S, revI a m i * vI b m i j =
      (∑ i ∈ S, if i < j then revI a m i * b ^ (m - i.val) else 0) +
        (if j ∈ S then revI a m j * b ^ (m - j.val) else 0) := by
    rw [Finset.sum_congr rfl (fun i _ => hsplit i), Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_ite_eq']
  have hθ : thetaI a m j * (revI a m j * b ^ (m - j.val)) = alpha a m * b ^ (m - j.val) := by
    unfold thetaI revI
    have : a ^ (j.val + 1) ≠ 0 := pow_ne_zero _ ha.ne'
    field_simp
  unfold CustAssort.AugGreedy.rev ChoiceCDLP.MNL.mnlObjective firstTerm secondTerm
  simp only [hN]
  rw [add_comm (∑ i ∈ S, vI b m i j) 1]
  have : thetaI a m j * (((∑ i ∈ S, if i < j then revI a m i * b ^ (m - i.val) else 0) +
        (if j ∈ S then revI a m j * b ^ (m - j.val) else 0)) / (1 + ∑ i ∈ S, vI b m i j))
      = (thetaI a m j * (∑ i ∈ S, if i < j then revI a m i * b ^ (m - i.val) else 0) +
        thetaI a m j * (if j ∈ S then revI a m j * b ^ (m - j.val) else 0)) /
          (1 + ∑ i ∈ S, vI b m i j) := by
    ring
  rw [this]
  by_cases hj : j ∈ S
  · simp only [hj, if_true]
    rw [hθ, add_div]
  · simp only [hj, if_false, mul_zero, add_zero, zero_div]

