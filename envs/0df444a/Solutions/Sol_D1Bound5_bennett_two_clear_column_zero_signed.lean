-- Prove2me | solution 1 for D1Bound5.bennett_two_clear_column_zero_signed
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:29:20.63376+00:00
-- url     : https://prove2.me/submissions/e8b12fa7-a76d-4f7a-a448-9bd9db97a212

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.Ring
import Theorems.Thm_D1Bound5_bennett_two_clear_column_zero

section
namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]









/-- Restoring the signs of the actual poles at zero. -/
theorem _root_.solution
    (a b c : F) (ha : a ≠ 0) (hb : b ≠ 0)
    (k d0 d1 d2 h0 h1 h2 : ℕ) (hk : 1 ≤ k)
    (hd : d0 + d1 + d2 = 1) (hh : h0 + h1 + h2 + 1 = k + d0) :
    (a * b * (a - b) ^ 2) ^ k * (a * b * c) ^ (k - h0) *
        ((-b)⁻¹) ^ (k + d1 + h1) * ((-a)⁻¹) ^ (k + d2 + h2) =
      (-1 : F) ^ ((k + d1 + h1) + (k + d2 + h2)) *
        (a ^ (d1 + h1) * b ^ (d2 + h2) * c ^ (k - h0) *
          (a - b) ^ (2 * k)) := by
  calc
    _ = (-1 : F) ^ ((k + d1 + h1) + (k + d2 + h2)) *
        ((a * b * (a - b) ^ 2) ^ k * (a * b * c) ^ (k - h0) *
          (b⁻¹) ^ (k + d1 + h1) * (a⁻¹) ^ (k + d2 + h2)) := by
      simp only [inv_neg]
      rw [show -(b⁻¹) = (-1 : F)*b⁻¹ by ring,
        show -(a⁻¹) = (-1 : F)*a⁻¹ by ring]
      simp only [mul_pow, pow_add]
      ring
    _ = _ := by rw [bennett_two_clear_column_zero a b c ha hb k d0 d1 d2 h0 h1 h2 hk hd hh]



end D1Bound5
end
