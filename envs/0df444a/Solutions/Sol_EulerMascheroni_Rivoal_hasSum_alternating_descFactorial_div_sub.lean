-- Prove2me | solution 1 for EulerMascheroni.Rivoal.hasSum_alternating_descFactorial_div_sub
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-25T21:21:40.262705+00:00
-- url     : https://prove2.me/submissions/50cc2786-21bc-4c28-bb21-2dc4934de82a

import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Data.Nat.Factorial.Basic
import Definitions.Def_eulerMascheroni_mixedCover

open Finset

theorem RivoalSeriesAux.ein_one_hasSum :
    HasSum (fun k : ℕ => (-1 : ℂ) ^ k / (((k + 1).factorial : ℂ) * ((k + 1 : ℕ) : ℂ)))
      (EulerMascheroni.Mixed.ein 1) := by
  have hs : Summable (fun k : ℕ => (-1 : ℂ) ^ k / (((k + 1).factorial : ℂ) * ((k + 1 : ℕ) : ℂ))) := by
    refine Summable.of_norm_bounded (Real.summable_pow_div_factorial 1) (fun k => ?_)
    rw [norm_div, norm_pow, norm_neg, norm_one, one_pow, norm_mul]
    simp only [Complex.norm_natCast]
    have h1 : (k.factorial : ℝ) ≤ ((k + 1).factorial : ℝ) := by
      exact_mod_cast Nat.factorial_le (by omega)
    have h2 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega)
    have h0 : (0 : ℝ) < k.factorial := by positivity
    rw [div_le_div_iff₀ (by positivity) h0]
    nlinarith
  convert hs.hasSum using 1
  unfold EulerMascheroni.Mixed.ein
  congr 1; funext k
  rw [one_pow, mul_one, mul_comm (((k + 1 : ℕ) : ℂ))]

theorem solution (j : ℕ) :
    HasSum (fun M : ℕ => if j < M then
        (-1 : ℂ) ^ M * (M.descFactorial j : ℂ) / ((M.factorial : ℂ) * ((M - j : ℕ) : ℂ)) else 0)
      (-(-1) ^ j * EulerMascheroni.Mixed.ein 1) := by
  rw [← hasSum_nat_add_iff' (j + 1)]
  have hz : ∑ i ∈ range (j + 1), (if j < i then
        (-1 : ℂ) ^ i * (i.descFactorial j : ℂ) / ((i.factorial : ℂ) * ((i - j : ℕ) : ℂ)) else 0) = 0 := by
    refine sum_eq_zero (fun i hi => ?_)
    rw [if_neg (by have := mem_range.mp hi; omega)]
  rw [hz, sub_zero]
  refine (RivoalSeriesAux.ein_one_hasSum.mul_left (-(-1 : ℂ) ^ j)).congr_fun ?_
  intro k
  rw [if_pos (by omega)]
  have h := Nat.factorial_mul_descFactorial (show j ≤ k + (j + 1) by omega)
  rw [show k + (j + 1) - j = k + 1 by omega] at h
  rw [show k + (j + 1) - j = k + 1 by omega]
  have hkj : ((k + (j + 1)).factorial : ℂ) =
      ((k + 1).factorial : ℂ) * ((k + (j + 1)).descFactorial j : ℂ) := by
    exact_mod_cast h.symm
  have hd : ((k + (j + 1)).descFactorial j : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_pos.mpr (by omega) |>.ne')
  have hk : ((k + 1).factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hk1 : ((k + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  rw [hkj, pow_add, pow_add]
  field_simp
