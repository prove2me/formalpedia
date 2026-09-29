-- Prove2me | solution 1 for BlockCycleRotation.gTerm_row_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:39:31.784278+00:00
-- url     : https://prove2.me/submissions/8ea6f646-11cd-49c1-b1aa-03b8c6760724

import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Definitions.Def_BlockCycleRotation_Remark21
import Theorems.Thm_BlockCycleRotation_sum_inv_sq_Ioc_le
import Theorems.Thm_BlockCycleRotation_sum_inv_shift_le
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

theorem sum_inv_sq_shift_le {a : ℕ} (ha : 0 < a) :
    ∑ a' ∈ Finset.Ico 1 a, 1 / ((a : ℝ) + (a' : ℝ)) ^ 2 ≤ 1 / (2 * (a : ℝ)) := by
  have haR : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hre : ∑ a' ∈ Finset.Ico 1 a, 1 / ((a : ℝ) + (a' : ℝ)) ^ 2
      = ∑ m ∈ Finset.Ioc a (2 * a - 1), 1 / ((m : ℝ)) ^ 2 := by
    refine Finset.sum_bij' (i := fun a' _ => a + a') (j := fun m _ => m - a) ?_ ?_ ?_ ?_ ?_
    · intro a' h
      rw [Finset.mem_Ico] at h
      rw [Finset.mem_Ioc]
      omega
    · intro m h
      rw [Finset.mem_Ioc] at h
      rw [Finset.mem_Ico]
      omega
    · intro a' h
      rw [Finset.mem_Ico] at h
      omega
    · intro m h
      rw [Finset.mem_Ioc] at h
      omega
    · intro a' h
      rw [Finset.mem_Ico] at h
      push_cast
      ring_nf
  rw [hre]
  have hle : a ≤ 2 * a - 1 := by omega
  have h := sum_inv_sq_Ioc_le ha (2 * a - 1) hle
  have hcast : ((2 * a - 1 : ℕ) : ℝ) = 2 * (a : ℝ) - 1 := by
    have : (1 : ℕ) ≤ 2 * a := by omega
    push_cast [Nat.cast_sub this]
    ring
  rw [hcast] at h
  have hpos : (0 : ℝ) < 2 * (a : ℝ) - 1 := by linarith
  have hstep : 1 / (a : ℝ) - 1 / (2 * (a : ℝ) - 1) ≤ 1 / (2 * (a : ℝ)) := by
    rw [div_sub_div _ _ (by linarith) (by linarith), div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  linarith

end BlockCycleRotation

open BlockCycleRotation in
/-- **`∑_{a'<a} gTerm ≤ 5/(8a²)`.** -/
theorem solution (a : ℕ) :
    ∑ a' ∈ Finset.range a, gTerm (a, a') ≤ 5 / (8 * (a : ℝ) ^ 2):= by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp [gTerm]
  · have haR : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
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
    have hb1 : 1 / (2 * (a : ℝ)) * (∑ a' ∈ Finset.Ico 1 a, 1 / ((a : ℝ) + (a' : ℝ)) ^ 2)
        ≤ 1 / (2 * (a : ℝ)) * (1 / (2 * (a : ℝ))) :=
      mul_le_mul_of_nonneg_left (sum_inv_sq_shift_le ha) (by positivity)
    have hb2 : 1 / (2 * (a : ℝ) ^ 2) * (∑ a' ∈ Finset.Ico 1 a, 1 / ((a : ℝ) + (a' : ℝ)))
        ≤ 1 / (2 * (a : ℝ) ^ 2) * (3 / 4) :=
      mul_le_mul_of_nonneg_left (sum_inv_shift_le a) (by positivity)
    have harith : 1 / (2 * (a : ℝ)) * (1 / (2 * (a : ℝ))) + 1 / (2 * (a : ℝ) ^ 2) * (3 / 4)
        = 5 / (8 * (a : ℝ) ^ 2) := by
      field_simp
      ring
    linarith
