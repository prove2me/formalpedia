-- Prove2me | solution 1 for AvramDividend.Classical.negative_jump_lk_integrand_lower
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T12:06:35.644285+00:00
-- url     : https://prove2.me/submissions/120b87d0-a479-427d-80b0-bab95768cb7c

import Mathlib

open MeasureTheory Set

theorem solution (θ y : ℝ) (hy : y < 0) :
    -((Iic (-1 : ℝ)).indicator (fun _ : ℝ => (1 : ℝ)) y) ≤
      Real.exp (θ * y) - 1 -
        θ * y * ((Ioo (-1 : ℝ) 1).indicator
          (fun _ : ℝ => (1 : ℝ)) y) := by
  by_cases hsmall : (-1 : ℝ) < y
  · have hIoo : y ∈ Ioo (-1 : ℝ) 1 := by
      simp only [Set.mem_Ioo]
      constructor
      · exact hsmall
      · linarith
    have hnot : y ∉ Iic (-1 : ℝ) := by
      intro h
      have hle : y ≤ (-1 : ℝ) := by
        simpa only [Set.mem_Iic] using h
      exact (not_le_of_gt hsmall) hle
    have hbase : (0 : ℝ) ≤ Real.exp (θ * y) - 1 - θ * y := by
      have he := Real.add_one_le_exp (θ * y)
      linarith
    simpa [Set.indicator, hnot, hIoo] using hbase
  · have hIic : y ∈ Iic (-1 : ℝ) := by
      simpa only [Set.mem_Iic] using (le_of_not_gt hsmall)
    have hnot : y ∉ Ioo (-1 : ℝ) 1 := by
      intro h
      have hl : (-1 : ℝ) < y := (Set.mem_Ioo.mp h).1
      exact hsmall hl
    have hbase : (-1 : ℝ) ≤ Real.exp (θ * y) - 1 := by
      have he := Real.exp_pos (θ * y)
      linarith
    simpa [Set.indicator, hIic, hnot] using hbase
