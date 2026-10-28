-- Prove2me | solution 1 for D1Bound5.bennettNegativeBinomial_mul
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:25:39.984165+00:00
-- url     : https://prove2.me/submissions/c73cce1e-98e6-4da5-bd99-61668223369a

import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.Ring

section
open PowerSeries

namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]





/-- The negative-integer binomial series is the formal inverse of `(1+X)^k`. -/
theorem _root_.solution (k : ℕ) :
    (1 + PowerSeries.X : PowerSeries F) ^ k * binomialSeries F (-(k : F)) = 1 := by
  rw [← binomialSeries_nat (R := F), ← binomialSeries_add]
  simp



end D1Bound5
end
