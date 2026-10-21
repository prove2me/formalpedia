-- Prove2me | solution 1 for DynFairDiv.Uniform.ffaTotal_uniform_monotone
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T12:07:04.13191+00:00
-- url     : https://prove2.me/submissions/da495d12-0963-4421-837a-b6a780c22764

import Mathlib
import Definitions.Def_DynFairDiv_Uniform_Model
import Theorems.Thm_DynFairDiv_Uniform_lemma_E_1

open DynFairDiv.Uniform

private lemma take_bound (d : ℕ) (hd : 1 ≤ d) (σ : ℝ) (hσ : 0 ≤ σ) (t : ℕ) :
    ((ffa (uniformCV d) σ t).take d).sum ≤
      ((min d t + 1 : ℕ) : ℝ) * (σ / ((t + 1 : ℕ) : ℝ)) := by
  obtain ⟨ℓ, i, hi, rfl⟩ : ∃ ℓ i, i ≤ d ∧ t = ℓ * (d + 1) + i :=
    ⟨t / (d + 1), t % (d + 1), by have := Nat.mod_lt t (show 0 < d + 1 by omega); omega,
      by have := Nat.div_add_mod t (d + 1); linarith [Nat.mul_comm (d + 1) (t / (d + 1))]⟩
  rw [lemma_E_1 d hd σ ℓ i hi]
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
  · simp only [List.range_zero, List.flatMap_nil, List.append_nil, zero_mul, zero_add]
    rw [List.take_of_length_le (by simp; omega), List.sum_replicate, min_eq_right hi,
      nsmul_eq_mul]
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · simp; positivity
    · have : ((i : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hi0.ne'
      have : ((i + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp
      rfl
  · obtain ⟨m, rfl⟩ : ∃ m, ℓ = m + 1 := ⟨ℓ - 1, by omega⟩
    rw [List.range_succ_eq_map, List.flatMap_cons, List.take_append, List.take_of_length_le
      (by simp; omega), List.length_replicate, List.take_append, List.take_replicate,
      min_eq_left (by omega), List.length_replicate,
      show d - i - (d + 1) = 0 by omega, List.take_zero, List.append_nil,
      List.sum_append, List.sum_replicate, List.sum_replicate, nsmul_eq_mul, nsmul_eq_mul,
      min_eq_left (by nlinarith)]
    push_cast [Nat.cast_sub hi]
    set M : ℝ := ((m : ℝ) + 1) * d + i with hM
    have hM1 : 1 ≤ M := by
      have : (1 : ℝ) ≤ d := by exact_mod_cast hd
      have : (0 : ℝ) ≤ m := by positivity
      have : (0 : ℝ) ≤ i := by positivity
      nlinarith
    have hid : (i : ℝ) ≤ d := by exact_mod_cast hi
    have h0 : (0 : ℝ) ≤ m := by positivity
    have e1 : ((m : ℝ) + 1) * d + i + 0 + 1 = M + 1 := by rw [hM]; ring
    have e2 : ((m : ℝ) + 1) * (d + 1) + i + 1 = M + (m + 1) + 1 := by rw [hM]; ring
    rw [e1, e2]
    rw [show (i : ℝ) * (σ / M) + ((d : ℝ) - i) * (σ / (M + 1)) =
      σ * ((i * (M + 1) + (d - i) * M) / (M * (M + 1))) by field_simp]
    rw [show ((d : ℝ) + 1) * (σ / (M + (m + 1) + 1)) = σ * ((d + 1) / (M + (m + 1) + 1)) by ring]
    apply mul_le_mul_of_nonneg_left _ hσ
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have key : ((d : ℝ) + 1) * (M * (M + 1)) - (i * (M + 1) + (d - i) * M) * (M + (m + 1) + 1)
        = (m + 1) * (d - i) := by rw [hM]; ring
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ m + 1) (by linarith : (0:ℝ) ≤ d - i)]

theorem solution (d : ℕ) (hd : 1 ≤ d) (σ : ℝ) (hσ : 0 ≤ σ) :
    Monotone (ffaTotal (uniformCV d) σ) := by
  apply monotone_nat_of_le_succ
  intro t
  unfold ffaTotal
  rw [ffa, List.sum_append, List.sum_replicate, nsmul_eq_mul]
  have h := take_bound d hd σ hσ t
  have h2 := List.sum_take_add_sum_drop (ffa (uniformCV d) σ t) d
  simp only [uniformCV] at h2 ⊢
  push_cast at h ⊢
  linarith
