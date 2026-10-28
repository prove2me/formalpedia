-- Prove2me | solution 1 for D1Bound5.bennettSeries_coeff_C_add_X_pow
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:23:56.701248+00:00
-- url     : https://prove2.me/submissions/f99b25c4-9513-4820-a47c-88b7968147c3

import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.Ring

section
open PowerSeries

namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]

/-- Polynomial binomial coefficients, viewed in formal power series. -/
theorem _root_.solution (a : F) (r h : ℕ) :
    PowerSeries.coeff h ((PowerSeries.C a + PowerSeries.X : PowerSeries F) ^ r) =
      a ^ (r - h) * (r.choose h : F) := by
  have hp : (PowerSeries.C a + PowerSeries.X : PowerSeries F) ^ r =
      (((Polynomial.C a + Polynomial.X : Polynomial F) ^ r).toPowerSeries) := by
    simp
  rw [hp, Polynomial.coeff_coe]
  simpa only [add_comm] using Polynomial.coeff_X_add_C_pow a r h



end D1Bound5
end
