-- Prove2me | solution 1 for D1Bound5.bennett_two_clear_column_one_signed
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:27:51.041971+00:00
-- url     : https://prove2.me/submissions/0249ba7a-c56f-4ba8-9f67-7561f26dabfb

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.Ring
import Theorems.Thm_D1Bound5_bennett_two_clear_column_one

section
namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]











/-- Restoring the sign of the actual pole `b-a` in column one. -/
theorem _root_.solution
    (a b c : F) (hb : b ≠ 0) (hab : a ≠ b)
    (k d0 d1 d2 h0 h1 h2 : ℕ) (hk : 1 ≤ k)
    (hd : d0 + d1 + d2 = 1) (hh : h0 + h1 + h2 + 1 = k + d1) :
    (a * b * (a - b) ^ 2) ^ k * (a * b * c + b) ^ (k - h1) *
        (b⁻¹) ^ (k + d0 + h0) * ((b - a)⁻¹) ^ (k + d2 + h2) =
      (-1 : F) ^ (k + d2 + h2) *
        (a ^ k * (a * c + 1) ^ (k - h1) * b ^ (d2 + h2) *
          (a - b) ^ (k - (d2 + h2))) := by
  have hneg : b - a = -(a - b) := by ring
  calc
    _ = (-1 : F) ^ (k + d2 + h2) *
        ((a * b * (a - b) ^ 2) ^ k * (a * b * c + b) ^ (k - h1) *
          (b⁻¹) ^ (k + d0 + h0) * ((a - b)⁻¹) ^ (k + d2 + h2)) := by
      rw [hneg]
      simp only [inv_neg]
      rw [show -((a-b)⁻¹) = (-1 : F)*(a-b)⁻¹ by ring]
      simp only [mul_pow]
      ring
    _ = _ := by rw [bennett_two_clear_column_one a b c hb hab k d0 d1 d2 h0 h1 h2 hk hd hh]

end D1Bound5
end
