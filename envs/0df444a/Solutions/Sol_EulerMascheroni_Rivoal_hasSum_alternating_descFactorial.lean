-- Prove2me | solution 1 for EulerMascheroni.Rivoal.hasSum_alternating_descFactorial
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-25T21:21:39.660334+00:00
-- url     : https://prove2.me/submissions/3b1750c9-60d7-4c85-9191-95c642ed4050

import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Data.Nat.Factorial.Basic

open Finset

theorem solution (j : ℕ) :
    HasSum (fun M : ℕ => (-1 : ℝ) ^ M * (M.descFactorial j : ℝ) / (M.factorial : ℝ))
      ((-1) ^ j * Real.exp (-1)) := by
  have hexp : HasSum (fun k : ℕ => (-1 : ℝ) ^ k / (k.factorial : ℝ)) (Real.exp (-1)) := by
    rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp (-1 : ℝ)
  rw [← hasSum_nat_add_iff' j]
  have hz : ∑ i ∈ range j, (-1 : ℝ) ^ i * (i.descFactorial j : ℝ) / (i.factorial : ℝ) = 0 := by
    refine sum_eq_zero (fun i hi => ?_)
    rw [Nat.descFactorial_eq_zero_iff_lt.mpr (mem_range.mp hi)]; simp
  rw [hz, sub_zero]
  refine (hexp.mul_left ((-1 : ℝ) ^ j)).congr_fun ?_
  intro k
  have h := Nat.factorial_mul_descFactorial (show j ≤ k + j by omega)
  rw [show k + j - j = k by omega] at h
  have hk : (k.factorial : ℝ) ≠ 0 := by positivity
  have hkj : ((k + j).factorial : ℝ) = (k.factorial : ℝ) * ((k + j).descFactorial j : ℝ) := by
    exact_mod_cast h.symm
  have hd : ((k + j).descFactorial j : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_pos.mpr (by omega) |>.ne')
  rw [hkj, pow_add]
  field_simp
