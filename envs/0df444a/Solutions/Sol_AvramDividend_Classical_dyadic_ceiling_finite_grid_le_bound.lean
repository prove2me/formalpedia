-- Prove2me | solution 1 for AvramDividend.Classical.dyadic_ceiling_finite_grid_le_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T21:43:34.383906+00:00
-- url     : https://prove2.me/submissions/a4e5065f-4b5d-4330-9266-384ef5831edf

import Mathlib
open scoped NNReal

theorem solution
    (H : ℝ≥0) (n : ℕ) :
    ∀ s ∈ (Finset.range (Nat.ceil ((H : ℝ) * (2 : ℝ) ^ n) + 1)).image
      (fun k : ℕ => (k : ℝ≥0) / (2 : ℝ≥0) ^ n), s ≤ H + 1 := by
  intro s hs
  simp only [Finset.mem_image, Finset.mem_range] at hs
  obtain ⟨k, hk, rfl⟩ := hs
  have hk' : (k : ℝ) ≤ (H : ℝ) * 2 ^ n + 1 := by
    have h1 : k ≤ Nat.ceil ((H : ℝ) * (2 : ℝ) ^ n) := Nat.lt_succ_iff.mp hk
    have h2 := Nat.ceil_lt_add_one (show (0:ℝ) ≤ (H : ℝ) * 2 ^ n by positivity)
    have : (k : ℝ) ≤ (Nat.ceil ((H : ℝ) * (2 : ℝ) ^ n) : ℝ) := by exact_mod_cast h1
    linarith
  rw [← NNReal.coe_le_coe]
  push_cast
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  have h1 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  rw [div_le_iff₀ hp]
  nlinarith [H.2]
