-- Prove2me | solution 1 for BlockCycleRotation.gTerm_row_ge
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T12:23:56.42994+00:00
-- url     : https://prove2.me/submissions/2c98b300-b8b3-487c-8999-d6aab9d48092

import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Definitions.Def_BlockCycleRotation_Remark21
import Theorems.Thm_BlockCycleRotation_sum_inv_sq_shift_ge
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

theorem sum_inv_shift_ge {a : ℕ} (ha : 1 ≤ a) :
    2 * ((a : ℝ) - 1) / (3 * (a : ℝ)) ≤ ∑ j ∈ Finset.Ico 1 a, 1 / ((a : ℝ) + (j : ℝ)) := by
  have haR : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hpair : ∀ j ∈ Finset.Ico 1 a,
      4 / (3 * (a : ℝ)) ≤ 1 / ((a : ℝ) + (j : ℝ)) + 1 / (2 * (a : ℝ) - (j : ℝ)) := by
    intro j h
    rw [Finset.mem_Ico] at h
    have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast h.1
    have hja : (j : ℝ) < (a : ℝ) := by exact_mod_cast h.2
    have hd1 : (0 : ℝ) < (a : ℝ) + (j : ℝ) := by linarith
    have hd2 : (0 : ℝ) < 2 * (a : ℝ) - (j : ℝ) := by linarith
    rw [div_add_div _ _ (ne_of_gt hd1) (ne_of_gt hd2), div_le_div_iff₀ (by positivity)
      (by positivity)]
    nlinarith [prod_shift_le (a := a) (j := j), hd1, hd2]
  have hdouble : (∑ j ∈ Finset.Ico 1 a, 1 / ((a : ℝ) + (j : ℝ)))
      + ∑ j ∈ Finset.Ico 1 a, 1 / (2 * (a : ℝ) - (j : ℝ))
      ≥ ((a : ℝ) - 1) * (4 / (3 * (a : ℝ))) := by
    rw [← Finset.sum_add_distrib]
    have hcard : ((a - 1 : ℕ) : ℝ) = (a : ℝ) - 1 := by
      push_cast [Nat.cast_sub ha]
      ring
    calc ((a : ℝ) - 1) * (4 / (3 * (a : ℝ)))
        = ∑ _j ∈ Finset.Ico 1 a, 4 / (3 * (a : ℝ)) := by
          rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, hcard]
      _ ≤ ∑ j ∈ Finset.Ico 1 a, (1 / ((a : ℝ) + (j : ℝ)) + 1 / (2 * (a : ℝ) - (j : ℝ))) :=
          Finset.sum_le_sum hpair
  rw [← sum_shift_reflect a (fun x => 1 / x)] at hdouble
  have ha0 : (0 : ℝ) < (a : ℝ) := by linarith
  have hrw : ((a : ℝ) - 1) * (4 / (3 * (a : ℝ))) = 2 * (2 * ((a : ℝ) - 1) / (3 * (a : ℝ))) := by
    field_simp
    ring
  rw [hrw] at hdouble
  linarith

end BlockCycleRotation

open BlockCycleRotation in
theorem solution {a : ℕ} (ha : 61 ≤ a) :
    (54 / 100 : ℝ) / (a : ℝ) ^ 2 ≤ ∑ a' ∈ Finset.range a, gTerm (a, a'):= by
  have ha1 : 1 ≤ a := by omega
  have haR : (61 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have ha0 : (0 : ℝ) < (a : ℝ) := by linarith
  have hrange : Finset.range a = insert 0 (Finset.Ico 1 a) := by
    ext k
    rw [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
    omega
  have h0 : gTerm (a, 0) = 0 := by simp [gTerm]
  rw [hrange, Finset.sum_insert (by simp), h0, zero_add]
  have hsplit : ∀ a' ∈ Finset.Ico 1 a, gTerm (a, a')
      = 1 / (2 * (a : ℝ)) * (1 / ((a : ℝ) + (a' : ℝ)) ^ 2)
        + 1 / (2 * (a : ℝ) ^ 2) * (1 / ((a : ℝ) + (a' : ℝ))) := by
    intro a' h
    rw [Finset.mem_Ico] at h
    unfold gTerm
    rw [if_pos ⟨h.1, h.2⟩]
    have haa : (0 : ℝ) < (a : ℝ) + (a' : ℝ) := by positivity
    field_simp
    ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hb1 : 1 / (2 * (a : ℝ)) * (4 * ((a : ℝ) - 1) / (9 * (a : ℝ) ^ 2))
      ≤ 1 / (2 * (a : ℝ)) * (∑ a' ∈ Finset.Ico 1 a, 1 / ((a : ℝ) + (a' : ℝ)) ^ 2) :=
    mul_le_mul_of_nonneg_left (sum_inv_sq_shift_ge ha1) (by positivity)
  have hb2 : 1 / (2 * (a : ℝ) ^ 2) * (2 * ((a : ℝ) - 1) / (3 * (a : ℝ)))
      ≤ 1 / (2 * (a : ℝ) ^ 2) * (∑ a' ∈ Finset.Ico 1 a, 1 / ((a : ℝ) + (a' : ℝ))) :=
    mul_le_mul_of_nonneg_left (sum_inv_shift_ge ha1) (by positivity)
  have harith : (54 / 100 : ℝ) / (a : ℝ) ^ 2
      ≤ 1 / (2 * (a : ℝ)) * (4 * ((a : ℝ) - 1) / (9 * (a : ℝ) ^ 2))
        + 1 / (2 * (a : ℝ) ^ 2) * (2 * ((a : ℝ) - 1) / (3 * (a : ℝ))) := by
    rw [div_le_iff₀ (by positivity)]
    have hexp : (1 / (2 * (a : ℝ)) * (4 * ((a : ℝ) - 1) / (9 * (a : ℝ) ^ 2))
        + 1 / (2 * (a : ℝ) ^ 2) * (2 * ((a : ℝ) - 1) / (3 * (a : ℝ)))) * (a : ℝ) ^ 2
        = 5 * ((a : ℝ) - 1) / (9 * (a : ℝ)) := by
      field_simp
      ring
    rw [hexp, le_div_iff₀ (by positivity)]
    linarith
  linarith
