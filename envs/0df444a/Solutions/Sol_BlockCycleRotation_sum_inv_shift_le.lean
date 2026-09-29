-- Prove2me | solution 1 for BlockCycleRotation.sum_inv_shift_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:38:50.8965+00:00
-- url     : https://prove2.me/submissions/6e9ec2dd-e990-4ddc-8b24-5142333930e4

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

end BlockCycleRotation

open BlockCycleRotation in
/-- **The reflection bound.**  `∑_{j=1}^{a-1} 1/(a+j) ≤ 3/4`, from
`1/(a+j) + 1/(2a-j) ≤ 3a/((a+1)(2a-1))`. -/
theorem solution (a : ℕ) :
    ∑ a' ∈ Finset.Ico 1 a, 1 / ((a : ℝ) + (a' : ℝ)) ≤ 3 / 4:= by
  rcases Nat.lt_or_ge a 2 with ha | ha
  · interval_cases a <;> norm_num
  · have haR : (2 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
    -- the reflected sum
    have hre : ∑ a' ∈ Finset.Ico 1 a, 1 / ((a : ℝ) + (a' : ℝ))
        = ∑ a' ∈ Finset.Ico 1 a, 1 / (2 * (a : ℝ) - (a' : ℝ)) := by
      refine Finset.sum_bij' (i := fun j _ => a - j) (j := fun j _ => a - j) ?_ ?_ ?_ ?_ ?_
      · intro j h
        rw [Finset.mem_Ico] at h ⊢
        omega
      · intro j h
        rw [Finset.mem_Ico] at h ⊢
        omega
      · intro j h
        rw [Finset.mem_Ico] at h
        omega
      · intro j h
        rw [Finset.mem_Ico] at h
        omega
      · intro j h
        rw [Finset.mem_Ico] at h
        have hcast : ((a - j : ℕ) : ℝ) = (a : ℝ) - (j : ℝ) := by
          push_cast [Nat.cast_sub (by omega : j ≤ a)]
          ring
        rw [hcast]
        ring_nf
    have hpair : ∀ j ∈ Finset.Ico 1 a,
        1 / ((a : ℝ) + (j : ℝ)) + 1 / (2 * (a : ℝ) - (j : ℝ))
          ≤ 3 * (a : ℝ) / (((a : ℝ) + 1) * (2 * (a : ℝ) - 1)) := by
      intro j h
      rw [Finset.mem_Ico] at h
      have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast h.1
      have hja : (j : ℝ) ≤ (a : ℝ) - 1 := by
        have : (j : ℝ) < (a : ℝ) := by exact_mod_cast h.2
        have hji : j + 1 ≤ a := by omega
        have : ((j + 1 : ℕ) : ℝ) ≤ (a : ℝ) := by exact_mod_cast hji
        push_cast at this
        linarith
      have hd1 : (0 : ℝ) < (a : ℝ) + (j : ℝ) := by linarith
      have hd2 : (0 : ℝ) < 2 * (a : ℝ) - (j : ℝ) := by linarith
      have hd3 : (0 : ℝ) < ((a : ℝ) + 1) * (2 * (a : ℝ) - 1) := by nlinarith
      have hprod : ((a : ℝ) + 1) * (2 * (a : ℝ) - 1)
          ≤ ((a : ℝ) + (j : ℝ)) * (2 * (a : ℝ) - (j : ℝ)) := by
        nlinarith [mul_nonneg (sub_nonneg.2 hj1) (sub_nonneg.2 hja)]
      rw [div_add_div _ _ (ne_of_gt hd1) (ne_of_gt hd2), div_le_div_iff₀ (by positivity) hd3]
      nlinarith
    have hsum : (∑ a' ∈ Finset.Ico 1 a, 1 / ((a : ℝ) + (a' : ℝ)))
        + ∑ a' ∈ Finset.Ico 1 a, 1 / (2 * (a : ℝ) - (a' : ℝ))
        ≤ ((a : ℕ) - 1 : ℕ) * (3 * (a : ℝ) / (((a : ℝ) + 1) * (2 * (a : ℝ) - 1))) := by
      rw [← Finset.sum_add_distrib]
      calc ∑ a' ∈ Finset.Ico 1 a, (1 / ((a : ℝ) + (a' : ℝ)) + 1 / (2 * (a : ℝ) - (a' : ℝ)))
          ≤ ∑ _a' ∈ Finset.Ico 1 a, 3 * (a : ℝ) / (((a : ℝ) + 1) * (2 * (a : ℝ) - 1)) :=
            Finset.sum_le_sum hpair
        _ = ((a - 1 : ℕ) : ℝ) * (3 * (a : ℝ) / (((a : ℝ) + 1) * (2 * (a : ℝ) - 1))) := by
            rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    have hcard : ((a - 1 : ℕ) : ℝ) = (a : ℝ) - 1 := by
      push_cast [Nat.cast_sub (by omega : 1 ≤ a)]
      ring
    rw [hcard] at hsum
    have hfin : ((a : ℝ) - 1) * (3 * (a : ℝ) / (((a : ℝ) + 1) * (2 * (a : ℝ) - 1))) ≤ 3 / 2 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by nlinarith) (by norm_num)]
      nlinarith
    rw [← hre] at hsum
    linarith
