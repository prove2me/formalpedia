-- Prove2me | solution 1 for D1Bound5.bennett_two_clear_column_two
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:30:27.714825+00:00
-- url     : https://prove2.me/submissions/95652166-c647-4322-be12-b6888c1a1c67

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.Ring
import Theorems.Thm_D1Bound5_bennett_cancel_power_denominator

section
namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]







/-- Column two of the two-anchor construction, with its exact `b^k`
divisibility and every surviving nonnegative difference exponent. -/
theorem _root_.solution
    (a b c : F) (ha : a ≠ 0) (hab : a ≠ b)
    (k d0 d1 d2 h0 h1 h2 : ℕ) (hk : 1 ≤ k)
    (hd : d0 + d1 + d2 = 1) (hh : h0 + h1 + h2 + 1 = k + d2) :
    (a * b * (a - b) ^ 2) ^ k * (a * b * c + a) ^ (k - h2) *
        (a⁻¹) ^ (k + d0 + h0) * ((a - b)⁻¹) ^ (k + d1 + h1) =
      b ^ k * (b * c + 1) ^ (k - h2) * a ^ (d1 + h1) *
        (a - b) ^ (k - (d1 + h1)) := by
  have hbase : a * b * c + a = a * (b * c + 1) := by ring
  have hA : a ^ k * a ^ (k - h2) * (a⁻¹) ^ (k + d0 + h0) =
      a ^ (d1 + h1) := by
    rw [← pow_add]
    apply bennett_cancel_power_denominator a ha
    omega
  have hD : (a - b) ^ (2 * k) * ((a - b)⁻¹) ^ (k + d1 + h1) =
      (a - b) ^ (k - (d1 + h1)) := by
    apply bennett_cancel_power_denominator (a - b) (sub_ne_zero.mpr hab)
    omega
  rw [hbase]
  calc
    _ = b ^ k * (b * c + 1) ^ (k - h2) *
        (a ^ k * a ^ (k - h2) * (a⁻¹) ^ (k + d0 + h0)) *
          ((a - b) ^ (2 * k) * ((a - b)⁻¹) ^ (k + d1 + h1)) := by
      simp only [mul_pow, ← pow_mul]
      ring
    _ = _ := by rw [hA, hD]





end D1Bound5
end
