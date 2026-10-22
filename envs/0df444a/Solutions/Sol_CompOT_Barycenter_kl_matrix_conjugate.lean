-- Prove2me | solution 1 for CompOT.Barycenter.kl_matrix_conjugate
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:02:40.981807+00:00
-- url     : https://prove2.me/submissions/91e9ad23-b159-4a12-9ed2-8ddc7a4a1db6

import Mathlib
import Definitions.Def_CompOT_Barycenter_Defs
set_option autoImplicit false
open CompOT.Barycenter

lemma ss_fy_le (u p k : ℝ) (hp : 0 ≤ p) (hk : 0 < k) :
    u * p - klEntry p k ≤ k * (Real.exp u - 1) := by
  unfold klEntry
  by_cases h0 : p = 0
  · subst h0
    have := Real.exp_pos u
    simp only [if_true, mul_zero]
    nlinarith
  · have hpos : 0 < p := lt_of_le_of_ne hp (Ne.symm h0)
    rw [if_neg h0]
    have hx : 0 < Real.exp u * k / p := by positivity
    have hle := Real.log_le_sub_one_of_pos hx
    have hlog : Real.log (Real.exp u * k / p) = u + Real.log k - Real.log p := by
      rw [Real.log_div (by positivity) h0, Real.log_mul (Real.exp_pos u).ne' hk.ne', Real.log_exp]
    rw [hlog] at hle
    have hlog2 : Real.log (p / k) = Real.log p - Real.log k := Real.log_div h0 hk.ne'
    rw [hlog2]
    have hm := mul_le_mul_of_nonneg_left hle hpos.le
    have e : p * (Real.exp u * k / p - 1) = Real.exp u * k - p := by field_simp
    rw [e] at hm
    nlinarith [hm]

lemma ss_fy_eq (u k : ℝ) (hk : 0 < k) :
    u * (k * Real.exp u) - klEntry (k * Real.exp u) k = k * (Real.exp u - 1) := by
  unfold klEntry
  have hp : k * Real.exp u ≠ 0 := by positivity
  rw [if_neg hp]
  have : k * Real.exp u / k = Real.exp u := by field_simp
  rw [this, Real.log_exp]
  ring

theorem solution {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m)
    (U K : Matrix (Fin n) (Fin m) ℝ) (hK : ∀ i j, 0 < K i j) :
    (∀ P : Matrix (Fin n) (Fin m) ℝ, (∀ i j, 0 ≤ P i j) →
      (∑ i, ∑ j, U i j * P i j) - klMatrix P K ≤
        ∑ i, ∑ j, K i j * (Real.exp (U i j) - 1)) ∧
    (∑ i, ∑ j, U i j * (K i j * Real.exp (U i j))) -
      klMatrix (fun i j => K i j * Real.exp (U i j)) K =
        ∑ i, ∑ j, K i j * (Real.exp (U i j) - 1) := by
  constructor
  · intro P hP
    unfold klMatrix
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum fun j _ => ss_fy_le _ _ _ (hP i j) (hK i j)
  · unfold klMatrix
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => ss_fy_eq _ _ (hK i j)
