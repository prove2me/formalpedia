-- Prove2me | solution 1 for D1Bound5.bennettHomogenizationTerm
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:33:48.710543+00:00
-- url     : https://prove2.me/submissions/16a77b72-b310-4627-8d2d-8d574c29c706

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.Ring

section
open Finset

namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]





/-- Exact homogenization of every monomial summand. -/
theorem _root_.solution (k h : ℕ) (hh : h ≤ k)
    (a N : F) (hN : N ≠ 0) :
    N ^ k * ((N⁻¹) ^ h * (1 + a * N⁻¹) ^ (k - h)) =
      (N + a) ^ (k - h) := by
  have hbase : 1 + a * N⁻¹ = (N + a) * N⁻¹ := by
    rw [add_mul, mul_inv_cancel₀ hN]
  rw [hbase, mul_pow]
  calc
    _ = (N ^ k * (N⁻¹) ^ (h + (k - h))) * (N + a) ^ (k - h) := by
      rw [pow_add]
      ring
    _ = _ := by
      rw [Nat.add_sub_of_le hh, ← mul_pow, mul_inv_cancel₀ hN, one_pow, one_mul]



section Nodes

variable {I : Type*} [DecidableEq I]







end Nodes

end D1Bound5
end
