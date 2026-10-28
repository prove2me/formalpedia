-- Prove2me | solution 1 for D1Bound5.bennett_two_clear_column_one
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:30:29.542285+00:00
-- url     : https://prove2.me/submissions/467267bd-1fb6-4aab-9c77-be4efba98d22

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.Ring
import Theorems.Thm_D1Bound5_bennett_cancel_power_denominator

section
namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]





/-- Column one of the two-anchor construction. The exact remaining factor
`a^k` is the column divisibility used by the arithmetic row-form argument. -/
theorem _root_.solution
    (a b c : F) (hb : b ≠ 0) (hab : a ≠ b)
    (k d0 d1 d2 h0 h1 h2 : ℕ) (hk : 1 ≤ k)
    (hd : d0 + d1 + d2 = 1) (hh : h0 + h1 + h2 + 1 = k + d1) :
    (a * b * (a - b) ^ 2) ^ k * (a * b * c + b) ^ (k - h1) *
        (b⁻¹) ^ (k + d0 + h0) * ((a - b)⁻¹) ^ (k + d2 + h2) =
      a ^ k * (a * c + 1) ^ (k - h1) * b ^ (d2 + h2) *
        (a - b) ^ (k - (d2 + h2)) := by
  have hbase : a * b * c + b = b * (a * c + 1) := by ring
  have hB : b ^ k * b ^ (k - h1) * (b⁻¹) ^ (k + d0 + h0) =
      b ^ (d2 + h2) := by
    rw [← pow_add]
    apply bennett_cancel_power_denominator b hb
    omega
  have hD : (a - b) ^ (2 * k) * ((a - b)⁻¹) ^ (k + d2 + h2) =
      (a - b) ^ (k - (d2 + h2)) := by
    apply bennett_cancel_power_denominator (a - b) (sub_ne_zero.mpr hab)
    omega
  rw [hbase]
  calc
    _ = a ^ k * (a * c + 1) ^ (k - h1) *
        (b ^ k * b ^ (k - h1) * (b⁻¹) ^ (k + d0 + h0)) *
          ((a - b) ^ (2 * k) * ((a - b)⁻¹) ^ (k + d2 + h2)) := by
      simp only [mul_pow, ← pow_mul]
      ring
    _ = _ := by rw [hB, hD]







end D1Bound5
end
