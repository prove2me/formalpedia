-- Prove2me | solution 1 for DbarRegularity.abs_inv_pow_sub_inv_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T19:39:10.346263+00:00
-- url     : https://prove2.me/submissions/fa57f73b-106d-42bb-a06e-71b04ca1a7f3

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Ring.Abs



namespace DbarRegularity

/-- Real-variable estimate: if `0 < a`, `2a ≤ c` and `|b - c| ≤ a`, then
`|b^{-d} - c^{-d}| ≤ 2 d 3^{d-1} a / c^{d+1}`. -/
theorem abs_inv_pow_sub_inv_pow_le (d : ℕ) {a b c : ℝ} (ha : 0 < a) (hc : 2 * a ≤ c)
    (hbc : |b - c| ≤ a) :
    |(b ^ d)⁻¹ - (c ^ d)⁻¹| ≤ 2 * d * 3 ^ (d - 1) * a / c ^ (d + 1) := by
  have hc0 : 0 < c := by linarith
  have hb1 : c / 2 ≤ b := by have := neg_abs_le (b - c); linarith
  have hb2 : b ≤ 3 * c / 2 := by have := le_abs_self (b - c); linarith
  have hb0 : 0 < b := by linarith
  have hbd : 0 < b ^ d := pow_pos hb0 d
  have hcd : 0 < c ^ d := pow_pos hc0 d
  have h1 : (b ^ d)⁻¹ - (c ^ d)⁻¹ = (c ^ d - b ^ d) / (b ^ d * c ^ d) := by
    field_simp
  rw [h1, abs_div, abs_of_pos (mul_pos hbd hcd)]
  have h2 : |c ^ d - b ^ d| ≤ a * d * (3 * c / 2) ^ (d - 1) := by
    refine (abs_pow_sub_pow_le c b d).trans ?_
    rw [abs_sub_comm] at hbc
    have hmax : max |c| |b| ≤ 3 * c / 2 := by
      rw [abs_of_pos hc0, abs_of_pos hb0]; exact max_le (by linarith) hb2
    gcongr
  have h3 : (c / 2) ^ d * c ^ d ≤ b ^ d * c ^ d := by gcongr
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  calc |c ^ d - b ^ d| / (b ^ d * c ^ d)
      ≤ a * d * (3 * c / 2) ^ (d - 1) / ((c / 2) ^ d * c ^ d) := by
        gcongr
    _ = 2 * d * 3 ^ (d - 1) * a / c ^ (d + 1) := by
        obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
        simp only [Nat.add_sub_cancel]
        rw [div_pow c 2, div_pow (3 * c) 2, mul_pow]
        field_simp
        ring

end DbarRegularity

open DbarRegularity

theorem solution (d : ℕ) {a b c : ℝ} (ha : 0 < a) (hc : 2 * a ≤ c)
    (hbc : |b - c| ≤ a) :
    |(b ^ d)⁻¹ - (c ^ d)⁻¹| ≤ 2 * d * 3 ^ (d - 1) * a / c ^ (d + 1) :=
  abs_inv_pow_sub_inv_pow_le d ha hc hbc
