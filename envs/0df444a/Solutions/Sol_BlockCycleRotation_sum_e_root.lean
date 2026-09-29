-- Prove2me | solution 1 for BlockCycleRotation.sum_e_root
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T10:35:08.912408+00:00
-- url     : https://prove2.me/submissions/ce345749-d0c4-431e-a62f-a5c2b3b5cb5f

import Definitions.Def_BlockCycleRotation_ExpSum
import Theorems.Thm_BlockCycleRotation_e_eq_one_iff
import Mathlib

open Real Finset

namespace BlockCycleRotation

@[simp]
theorem norm_e (θ : ℝ) : ‖e θ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

@[simp]
theorem norm_e_pow (θ : ℝ) (n : ℕ) : ‖e θ ^ n‖ = 1 := by
  rw [norm_pow, norm_e, one_pow]

@[simp]
theorem e_zero : e 0 = 1 := by simp [e]

/-- `e` turns multiplication by a natural number into a power. -/
theorem e_pow (θ : ℝ) (n : ℕ) : e θ ^ n = e (n * θ) := by
  rw [e, e, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

end BlockCycleRotation

open BlockCycleRotation in
/-- **Orthogonality.**  `∑_{m < a} e(2πmr/a)` is `a` when `a ∣ r` and `0` otherwise. -/
theorem solution {a : ℕ} (ha : 0 < a) (r : ℤ) :
    ∑ _m ∈ Finset.range a, (e (2 * π * r / a)) ^ _m
      = if (a : ℤ) ∣ r then (a : ℂ) else 0:= by
  have hane : ((a : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 ha.ne'
  have hpi : (2 : ℝ) * π ≠ 0 := by have := Real.pi_pos; positivity
  by_cases hd : (a : ℤ) ∣ r
  · rw [if_pos hd]
    obtain ⟨t, ht⟩ := hd
    have hx : e (2 * π * (r : ℝ) / a) = 1 := by
      rw [e_eq_one_iff]
      refine ⟨t, ?_⟩
      have hr : (r : ℝ) = (a : ℝ) * (t : ℝ) := by
        exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) ht
      rw [hr]
      field_simp
    rw [hx]
    simp
  · rw [if_neg hd]
    have hx1 : e (2 * π * (r : ℝ) / a) ≠ 1 := by
      intro hcon
      rw [e_eq_one_iff] at hcon
      obtain ⟨n, hn⟩ := hcon
      refine hd ⟨n, ?_⟩
      rw [div_eq_iff hane] at hn
      have hcancel : (2 * π) * (r : ℝ) = (2 * π) * ((a : ℝ) * (n : ℝ)) := by
        calc (2 * π) * (r : ℝ) = 2 * π * (r : ℝ) := by ring
          _ = 2 * π * (n : ℝ) * a := hn
          _ = (2 * π) * ((a : ℝ) * (n : ℝ)) := by ring
      have h2 : (r : ℝ) = (a : ℝ) * (n : ℝ) := mul_left_cancel₀ hpi hcancel
      exact_mod_cast h2
    have hxa : e (2 * π * (r : ℝ) / a) ^ a = 1 := by
      rw [e_pow]
      have hcalc : (a : ℝ) * (2 * π * (r : ℝ) / a) = 2 * π * (r : ℝ) := by
        field_simp
      rw [hcalc, e_eq_one_iff]
      exact ⟨r, rfl⟩
    rw [geom_sum_eq hx1, hxa]
    simp
