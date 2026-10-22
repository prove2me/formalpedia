-- Prove2me | solution 1 for GenEmpLik.Consistency.display_after_47
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T10:58:12.40999+00:00
-- url     : https://prove2.me/submissions/34169c6e-426d-46b3-a858-8de7a82e4874

import Mathlib
import Definitions.Def_PhiDivRobust_Counterpart_uncertaintySet

set_option autoImplicit false

theorem lr_le_l2 {n : ℕ} (v : Fin n → ℝ) (r : ℝ) (hr : 2 ≤ r) :
    (∑ i, |v i| ^ r) ^ (1 / r) ≤ Real.sqrt (∑ i, (v i) ^ 2) := by
  set Q : ℝ := ∑ i, (v i) ^ 2 with hQ
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun i _ => sq_nonneg _
  set s : ℝ := Real.sqrt Q with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsQ : s ^ 2 = Q := Real.sq_sqrt hQ0
  have hrpos : 0 < r := by linarith
  have hterm : ∀ i, |v i| ^ r ≤ (v i) ^ 2 * s ^ (r - 2) := by
    intro i
    have hle : |v i| ≤ s := by
      rw [hs]
      apply Real.abs_le_sqrt
      exact Finset.single_le_sum (f := fun i => (v i) ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    have h1 : |v i| ^ r = |v i| ^ (2 : ℝ) * |v i| ^ (r - 2) := by
      rw [← Real.rpow_add' (abs_nonneg _) (by linarith)]
      congr 1; ring
    have h2 : |v i| ^ (r - 2) ≤ s ^ (r - 2) :=
      Real.rpow_le_rpow (abs_nonneg _) hle (by linarith)
    have h3 : |v i| ^ (2 : ℝ) = (v i) ^ 2 := by
      rw [Real.rpow_two, sq_abs]
    rw [h1, h3]
    exact mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
  have hsum : ∑ i, |v i| ^ r ≤ s ^ r := by
    calc ∑ i, |v i| ^ r ≤ ∑ i, (v i) ^ 2 * s ^ (r - 2) := Finset.sum_le_sum fun i _ => hterm i
      _ = Q * s ^ (r - 2) := by rw [← Finset.sum_mul]
      _ = s ^ (2 : ℝ) * s ^ (r - 2) := by rw [Real.rpow_two, hsQ]
      _ = s ^ r := by
        rw [← Real.rpow_add' hs0 (by linarith)]
        congr 1; ring
  have hnn : 0 ≤ ∑ i, |v i| ^ r := Finset.sum_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg _) _
  calc (∑ i, |v i| ^ r) ^ (1 / r) ≤ (s ^ r) ^ (1 / r) :=
        Real.rpow_le_rpow hnn hsum (by positivity)
    _ = s := by
        rw [← Real.rpow_mul hs0]
        rw [mul_one_div_cancel hrpos.ne', Real.rpow_one]

theorem solution (f : ℝ → EReal) (ρ : ℝ) (n : ℕ) (hn : 0 < n) (r : ℝ) (hr : 2 ≤ r)
    (Cf : ℝ)
    (hCf : ∀ w ∈ PhiDivRobust.Counterpart.probUncertaintySet f
        (fun _ : Fin n => (1 : ℝ) / n) (ρ / n),
      Real.sqrt (∑ i, ((n : ℝ) * w i - 1) ^ 2) ≤ Real.sqrt (ρ * Cf))
    (w : Fin n → ℝ) (hw : w ∈ PhiDivRobust.Counterpart.probUncertaintySet f
      (fun _ : Fin n => (1 : ℝ) / n) (ρ / n)) :
    ((1 / (n : ℝ)) * ∑ i, |(n : ℝ) * w i - 1| ^ r) ^ (1 / r) =
        (n : ℝ) ^ (-(1 / r)) * (∑ i, |(n : ℝ) * w i - 1| ^ r) ^ (1 / r) ∧
      (n : ℝ) ^ (-(1 / r)) * (∑ i, |(n : ℝ) * w i - 1| ^ r) ^ (1 / r) ≤
        (n : ℝ) ^ (-(1 / r)) * Real.sqrt (∑ i, ((n : ℝ) * w i - 1) ^ 2) ∧
      (n : ℝ) ^ (-(1 / r)) * Real.sqrt (∑ i, ((n : ℝ) * w i - 1) ^ 2) ≤
        (n : ℝ) ^ (-(1 / r)) * Real.sqrt (ρ * Cf) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hS : 0 ≤ ∑ i, |(n : ℝ) * w i - 1| ^ r :=
    Finset.sum_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg _) _
  have hpow : (0 : ℝ) ≤ (n : ℝ) ^ (-(1 / r)) := by positivity
  refine ⟨?_, ?_, ?_⟩
  · rw [Real.mul_rpow (by positivity) hS, one_div, Real.inv_rpow hnpos.le, Real.rpow_neg hnpos.le]
  · exact mul_le_mul_of_nonneg_left (lr_le_l2 (fun i => (n : ℝ) * w i - 1) r hr) hpow
  · exact mul_le_mul_of_nonneg_left (hCf w hw) hpow
