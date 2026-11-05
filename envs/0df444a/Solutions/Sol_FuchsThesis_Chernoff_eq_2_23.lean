-- Prove2me | solution 1 for FuchsThesis.Chernoff.eq_2_23
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T15:03:31.042246+00:00
-- url     : https://prove2.me/submissions/bb21d0da-a331-45b1-991b-b85ed5eb9ff1

import Mathlib

theorem solution (a b α : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    min a b ≤ a ^ α * b ^ (1 - α) := by
  let m := min a b
  have hm0 : 0 ≤ m := le_min ha hb
  have hma : m ≤ a := min_le_left _ _
  have hmb : m ≤ b := min_le_right _ _
  have hβ : 0 ≤ 1 - α := sub_nonneg.mpr hα1
  have h1 : m ^ α ≤ a ^ α := Real.rpow_le_rpow hm0 hma hα0
  have h2 : m ^ (1 - α) ≤ b ^ (1 - α) :=
    Real.rpow_le_rpow hm0 hmb hβ
  have hmul : m ^ α * m ^ (1 - α) ≤ a ^ α * b ^ (1 - α) :=
    mul_le_mul h1 h2 (Real.rpow_nonneg hm0 _) (Real.rpow_nonneg ha _)
  have hpow : m ^ α * m ^ (1 - α) = m := by
    rw [← Real.rpow_add_of_nonneg hm0 hα0 hβ]
    have : α + (1 - α) = (1 : ℝ) := by ring
    rw [this, Real.rpow_one]
  change m ≤ a ^ α * b ^ (1 - α)
  rw [← hpow]
  exact hmul
