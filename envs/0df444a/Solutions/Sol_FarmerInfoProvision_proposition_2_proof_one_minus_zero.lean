-- Prove2me | solution 1 for FarmerInfoProvision.proposition_2_proof_one_minus_zero
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T00:41:21.379256+00:00
-- url     : https://prove2.me/submissions/74ea87ab-a545-4d41-ba75-50af52b4d920

import Mathlib
import Definitions.Def_FarmerInfoProvision_totalWelfare
import Definitions.Def_FarmerInfoProvision_provisionIndex

open FarmerInfoProvision in
theorem solution {n : ℕ} (hn : 4 ≤ n) {a b c α β γ : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hα : 0 < α) (hβ : 0 < β) (hγ : 0 ≤ γ) :
    totalWelfare a b c (n : ℝ) 1 α β γ - totalWelfare a b c (n : ℝ) 0 α β γ =
      β * provisionIndex (n : ℝ) α β γ /
        (b * (2 * α + γ + (n : ℝ) * γ) ^ 2 *
          (4 * α ^ 2 + (1 + (n : ℝ)) * γ * (β + γ) + 2 * α * (2 * β + (2 + (n : ℝ)) * γ)) ^ 2) := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hΨ : ∀ n1 : ℝ, 0 ≤ n1 → 0 < Psi (n : ℝ) n1 α β γ := by
    intro n1 hn1
    unfold Psi
    have t1 : 0 < 4 * (n1 + 1) * α ^ 2 := mul_pos (mul_pos four_pos (by linarith)) (pow_pos hα 2)
    have t2 : 0 ≤ ((n : ℝ) + 1) * γ * ((n1 + 1) * γ + 2 * β) :=
      mul_nonneg (mul_nonneg (by linarith) hγ)
        (add_nonneg (mul_nonneg (by linarith) hγ) (by linarith))
    have t3 : 0 ≤ 2 * (n1 + 1) * α * (((n : ℝ) + 2) * γ + 2 * β) :=
      mul_nonneg (mul_nonneg (mul_nonneg two_pos.le (by linarith)) hα.le)
        (add_nonneg (mul_nonneg (by linarith) hγ) (by linarith))
    linarith
  have hΨ1 := (hΨ 1 zero_le_one).ne'
  have hΨ0 := (hΨ 0 le_rfl).ne'
  have hD1 : (2 * α + γ + (n : ℝ) * γ) ≠ 0 := by
    have := mul_nonneg hn0 hγ
    linarith
  have hD2 : (4 * α ^ 2 + (1 + (n : ℝ)) * γ * (β + γ) + 2 * α * (2 * β + (2 + (n : ℝ)) * γ)) ≠ 0 := by
    have t1 : 0 < 4 * α ^ 2 := by positivity
    have t2 : 0 ≤ (1 + (n : ℝ)) * γ * (β + γ) :=
      mul_nonneg (mul_nonneg (by linarith) hγ) (by linarith)
    have t3 : 0 ≤ 2 * α * (2 * β + (2 + (n : ℝ)) * γ) :=
      mul_nonneg (mul_nonneg two_pos.le hα.le) (add_nonneg (by linarith) (mul_nonneg (by linarith) hγ))
    linarith
  have hn1 : (n : ℝ) + 1 ≠ 0 := by linarith
  have hb0 := hb.ne'
  have hα0 := hα.ne'
  have hβ0 := hβ.ne'
  unfold totalWelfare profitInformed profitUninformed coefA0 coefA1 coefA2 coefB1 provisionIndex
  rcases hγ.eq_or_lt with h0 | hpos
  · subst h0
    simp only [div_zero, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_div]
    unfold Psi at hΨ1 hΨ0 ⊢
    field_simp
    ring
  · have hγ0 := hpos.ne'
    field_simp
    unfold Psi
    ring
