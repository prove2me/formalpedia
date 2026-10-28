-- Prove2me | solution 1 for D1Bound5.bennett_two_clear_column_zero
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:30:32.502981+00:00
-- url     : https://prove2.me/submissions/61de7b0e-5c14-49ce-96b7-db0d0610c08f

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.Ring
import Theorems.Thm_D1Bound5_bennett_cancel_power_denominator

section
namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]



/-- Column zero of the two-anchor construction: clearing the pole denominators
leaves an ordinary polynomial monomial. The omitted signs and generalized
choose factors are scalar factors, handled independently. -/
theorem _root_.solution
    (a b c : F) (ha : a ≠ 0) (hb : b ≠ 0)
    (k d0 d1 d2 h0 h1 h2 : ℕ) (hk : 1 ≤ k)
    (hd : d0 + d1 + d2 = 1) (hh : h0 + h1 + h2 + 1 = k + d0) :
    (a * b * (a - b) ^ 2) ^ k * (a * b * c) ^ (k - h0) *
        (b⁻¹) ^ (k + d1 + h1) * (a⁻¹) ^ (k + d2 + h2) =
      a ^ (d1 + h1) * b ^ (d2 + h2) * c ^ (k - h0) *
        (a - b) ^ (2 * k) := by
  have hA : a ^ k * a ^ (k - h0) * (a⁻¹) ^ (k + d2 + h2) =
      a ^ (d1 + h1) := by
    rw [← pow_add]
    apply bennett_cancel_power_denominator a ha
    omega
  have hB : b ^ k * b ^ (k - h0) * (b⁻¹) ^ (k + d1 + h1) =
      b ^ (d2 + h2) := by
    rw [← pow_add]
    apply bennett_cancel_power_denominator b hb
    omega
  calc
    _ = (a ^ k * a ^ (k - h0) * (a⁻¹) ^ (k + d2 + h2)) *
        (b ^ k * b ^ (k - h0) * (b⁻¹) ^ (k + d1 + h1)) *
          c ^ (k - h0) * (a - b) ^ (2 * k) := by
      simp only [mul_pow, ← pow_mul]
      ring
    _ = _ := by rw [hA, hB]









end D1Bound5
end
