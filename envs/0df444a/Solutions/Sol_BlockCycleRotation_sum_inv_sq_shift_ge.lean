-- Prove2me | solution 1 for BlockCycleRotation.sum_inv_sq_shift_ge
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T12:22:14.171763+00:00
-- url     : https://prove2.me/submissions/c38dc260-a291-4957-b583-8ea316003961

import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Mathlib

open Real Finset Filter Topology

namespace BlockCycleRotation

@[simp]
theorem remSum_zero (n : ℕ) : remSum n 0 = 0 := by
  rw [remSum]; simp

@[simp]
theorem norm_e (θ : ℝ) : ‖e θ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

@[simp]
theorem norm_e_pow (θ : ℝ) (n : ℕ) : ‖e θ ^ n‖ = 1 := by
  rw [norm_pow, norm_e, one_pow]

@[simp]
theorem e_zero : e 0 = 1 := by simp [e]

@[simp] theorem K_nil : K [] = 1 := rfl

@[simp] theorem K_singleton (c : ℕ) : K [c] = c := rfl

@[simp] theorem cf_zero (a : ℕ) : cf a 0 = [] := by rw [cf]; simp

theorem sum_shift_reflect (a : ℕ) (f : ℝ → ℝ) :
    ∑ j ∈ Finset.Ico 1 a, f ((a : ℝ) + (j : ℝ))
      = ∑ j ∈ Finset.Ico 1 a, f (2 * (a : ℝ) - (j : ℝ)) := by
  refine Finset.sum_bij' (i := fun j _ => a - j) (j := fun j _ => a - j) ?_ ?_ ?_ ?_ ?_
  · intro j h; rw [Finset.mem_Ico] at h ⊢; omega
  · intro j h; rw [Finset.mem_Ico] at h ⊢; omega
  · intro j h; rw [Finset.mem_Ico] at h; omega
  · intro j h; rw [Finset.mem_Ico] at h; omega
  · intro j h
    rw [Finset.mem_Ico] at h
    have hcast : ((a - j : ℕ) : ℝ) = (a : ℝ) - (j : ℝ) := by
      push_cast [Nat.cast_sub (by omega : j ≤ a)]
      ring
    rw [hcast]
    congr 1
    ring

theorem prod_shift_le {a : ℕ} {j : ℕ} :
    ((a : ℝ) + (j : ℝ)) * (2 * (a : ℝ) - (j : ℝ)) ≤ 9 / 4 * (a : ℝ) ^ 2 := by
  nlinarith [sq_nonneg ((j : ℝ) - (a : ℝ) / 2)]

end BlockCycleRotation

open BlockCycleRotation in
theorem solution {a : ℕ} (ha : 1 ≤ a) :
    4 * ((a : ℝ) - 1) / (9 * (a : ℝ) ^ 2)
      ≤ ∑ j ∈ Finset.Ico 1 a, 1 / ((a : ℝ) + (j : ℝ)) ^ 2:= by
  have haR : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hpair : ∀ j ∈ Finset.Ico 1 a,
      8 / (9 * (a : ℝ) ^ 2)
        ≤ 1 / ((a : ℝ) + (j : ℝ)) ^ 2 + 1 / (2 * (a : ℝ) - (j : ℝ)) ^ 2 := by
    intro j h
    rw [Finset.mem_Ico] at h
    have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast h.1
    have hja : (j : ℝ) < (a : ℝ) := by exact_mod_cast h.2
    have hd1 : (0 : ℝ) < (a : ℝ) + (j : ℝ) := by linarith
    have hd2 : (0 : ℝ) < 2 * (a : ℝ) - (j : ℝ) := by linarith
    have hprod := prod_shift_le (a := a) (j := j)
    have hamgm : 2 / (((a : ℝ) + (j : ℝ)) * (2 * (a : ℝ) - (j : ℝ)))
        ≤ 1 / ((a : ℝ) + (j : ℝ)) ^ 2 + 1 / (2 * (a : ℝ) - (j : ℝ)) ^ 2 := by
      rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
        (by positivity)]
      nlinarith [mul_nonneg (mul_pos hd1 hd2).le
        (sq_nonneg (((a : ℝ) + (j : ℝ)) - (2 * (a : ℝ) - (j : ℝ))))]
    have hstep : 8 / (9 * (a : ℝ) ^ 2)
        ≤ 2 / (((a : ℝ) + (j : ℝ)) * (2 * (a : ℝ) - (j : ℝ))) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hprod]
    linarith
  have hdouble : (∑ j ∈ Finset.Ico 1 a, 1 / ((a : ℝ) + (j : ℝ)) ^ 2)
      + ∑ j ∈ Finset.Ico 1 a, 1 / (2 * (a : ℝ) - (j : ℝ)) ^ 2
      ≥ ((a : ℝ) - 1) * (8 / (9 * (a : ℝ) ^ 2)) := by
    rw [← Finset.sum_add_distrib]
    have hcard : ((a - 1 : ℕ) : ℝ) = (a : ℝ) - 1 := by
      push_cast [Nat.cast_sub ha]
      ring
    calc ((a : ℝ) - 1) * (8 / (9 * (a : ℝ) ^ 2))
        = ∑ _j ∈ Finset.Ico 1 a, 8 / (9 * (a : ℝ) ^ 2) := by
          rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, hcard]
      _ ≤ ∑ j ∈ Finset.Ico 1 a,
            (1 / ((a : ℝ) + (j : ℝ)) ^ 2 + 1 / (2 * (a : ℝ) - (j : ℝ)) ^ 2) :=
          Finset.sum_le_sum hpair
  rw [← sum_shift_reflect a (fun x => 1 / x ^ 2)] at hdouble
  have ha0 : (0 : ℝ) < (a : ℝ) := by linarith
  have hrw : ((a : ℝ) - 1) * (8 / (9 * (a : ℝ) ^ 2))
      = 2 * (4 * ((a : ℝ) - 1) / (9 * (a : ℝ) ^ 2)) := by
    field_simp
    ring
  rw [hrw] at hdouble
  linarith
