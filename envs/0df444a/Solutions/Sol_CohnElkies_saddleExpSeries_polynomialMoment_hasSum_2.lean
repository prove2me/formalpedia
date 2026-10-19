-- Prove2me | solution 2 for CohnElkies.saddleExpSeries_polynomialMoment_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:05:39.492988+00:00
-- url     : https://prove2.me/submissions/18d66cec-902d-44c8-aff3-4e1b68f99b36

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


theorem solution (y : ℝ) :
    HasSum
      (fun n : ℕ =>
        ((n : ℝ) + (n : ℝ) ^ 2) *
          (y ^ n / (n.factorial : ℝ)))
      ((2 * y + y ^ 2) * Real.exp y) := by
  have hE : HasSum (fun n : ℕ => y ^ n / (n.factorial : ℝ)) (Real.exp y) := by
    rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp y
  have hH : HasSum (fun n : ℕ => (n : ℝ) * (y ^ n / (n.factorial : ℝ))) (y * Real.exp y) := by
    have hf : (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * (y ^ (n + 1) / ((n + 1).factorial : ℝ))) =
        fun n : ℕ => y * (y ^ n / (n.factorial : ℝ)) := by
      funext n
      rw [Nat.factorial_succ, pow_succ]
      push_cast
      have : (0:ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
      field_simp
      try ring
    have hv : y * Real.exp y - ∑ i ∈ Finset.range 1, (i : ℝ) * (y ^ i / (i.factorial : ℝ)) =
        y * Real.exp y := by simp
    have h' : HasSum (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * (y ^ (n + 1) / ((n + 1).factorial : ℝ)))
        (y * Real.exp y - ∑ i ∈ Finset.range 1, (i : ℝ) * (y ^ i / (i.factorial : ℝ))) := by
      rw [hv, hf]; exact hE.mul_left y
    exact (hasSum_nat_add_iff' 1).1 h'
  have hG : HasSum (fun n : ℕ => (n : ℝ) * ((n : ℝ) - 1) * (y ^ n / (n.factorial : ℝ)))
      (y ^ 2 * Real.exp y) := by
    have hf : (fun n : ℕ => ((n + 2 : ℕ) : ℝ) * (((n + 2 : ℕ) : ℝ) - 1) *
        (y ^ (n + 2) / ((n + 2).factorial : ℝ))) =
        fun n : ℕ => y ^ 2 * (y ^ n / (n.factorial : ℝ)) := by
      funext n
      rw [show n + 2 = (n + 1) + 1 from rfl, Nat.factorial_succ, Nat.factorial_succ, pow_succ, pow_succ]
      push_cast
      have : (0:ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
      field_simp
      try ring
    have hv : y ^ 2 * Real.exp y - ∑ i ∈ Finset.range 2,
        (i : ℝ) * ((i : ℝ) - 1) * (y ^ i / (i.factorial : ℝ)) = y ^ 2 * Real.exp y := by
      simp [Finset.sum_range_succ]
    have h' : HasSum (fun n : ℕ => ((n + 2 : ℕ) : ℝ) * (((n + 2 : ℕ) : ℝ) - 1) *
        (y ^ (n + 2) / ((n + 2).factorial : ℝ)))
        (y ^ 2 * Real.exp y - ∑ i ∈ Finset.range 2,
          (i : ℝ) * ((i : ℝ) - 1) * (y ^ i / (i.factorial : ℝ))) := by
      rw [hv, hf]; exact hE.mul_left (y ^ 2)
    exact (hasSum_nat_add_iff' 2).1 h'
  have hF : (fun n : ℕ => ((n : ℝ) + (n : ℝ) ^ 2) * (y ^ n / (n.factorial : ℝ))) =
      fun n : ℕ => (n : ℝ) * ((n : ℝ) - 1) * (y ^ n / (n.factorial : ℝ)) +
        2 * ((n : ℝ) * (y ^ n / (n.factorial : ℝ))) := by
    funext n; ring
  rw [hF, show (2 * y + y ^ 2) * Real.exp y = y ^ 2 * Real.exp y + 2 * (y * Real.exp y) by ring]
  exact hG.add (hH.mul_left 2)

