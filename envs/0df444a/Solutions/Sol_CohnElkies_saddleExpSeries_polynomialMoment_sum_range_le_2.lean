-- Prove2me | solution 2 for CohnElkies.saddleExpSeries_polynomialMoment_sum_range_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:28:14.834379+00:00
-- url     : https://prove2.me/submissions/f6e899f1-1533-42ec-a6f0-5f681768ef3a

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology


theorem solution
    {y : ℝ} (hy : 0 ≤ y) (N : ℕ) :
    (∑ n ∈ Finset.range N,
      ((n : ℝ) + (n : ℝ) ^ 2) *
        (y ^ n / (n.factorial : ℝ))) ≤
      (2 * y + y ^ 2) * Real.exp y := by
  have hexp : HasSum (fun n : ℕ => y ^ n / (n.factorial : ℝ)) (Real.exp y) := by
    rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp y
  have h2 : HasSum (fun n : ℕ => (n : ℝ) * ((n : ℝ) - 1) * (y ^ n / (n.factorial : ℝ))) (y ^ 2 * Real.exp y) := by
    rw [← hasSum_nat_add_iff' 2]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
    refine (hexp.mul_left (y ^ 2)).congr_fun ?_
    intro n
    rw [Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    have hf : (n.factorial : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  have h1 : HasSum (fun n : ℕ => (n : ℝ) * (y ^ n / (n.factorial : ℝ))) (y * Real.exp y) := by
    rw [← hasSum_nat_add_iff' 1]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
    refine (hexp.mul_left y).congr_fun ?_
    intro n
    rw [Nat.factorial_succ]
    push_cast
    have hf : (n.factorial : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  have hs := (h1.mul_left 2).add h2
  have hs' : HasSum (fun n : ℕ => ((n : ℝ) + (n : ℝ) ^ 2) * (y ^ n / (n.factorial : ℝ)))
      ((2 * y + y ^ 2) * Real.exp y) := by
    rw [show (2 * y + y ^ 2) * Real.exp y = 2 * (y * Real.exp y) + y ^ 2 * Real.exp y by ring]
    exact hs.congr_fun (fun n => by ring)
  refine sum_le_hasSum _ (fun n _ => ?_) hs'
  positivity

