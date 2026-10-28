-- Prove2me | solution 1 for D1Bound5.bennett_coeff_mul_trunc
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:58:26.389606+00:00
-- url     : https://prove2.me/submissions/b4266fd0-6762-4f55-ac34-e8dd3b5ba32e

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.Ring

section
open Finset

namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]



section Nodes

variable {I : Type*} [Fintype I] [DecidableEq I]



/-- Truncating a multiplier preserves every coefficient below the truncation
order, even when the other factor is an infinite series. -/
theorem _root_.solution (P θ : PowerSeries F) (D r : ℕ) (hr : r < D) :
    PowerSeries.coeff r (P * (PowerSeries.trunc D θ : PowerSeries F)) =
      PowerSeries.coeff r (P * θ) := by
  calc
    _ = PowerSeries.coeff r
        (PowerSeries.trunc D (P * (PowerSeries.trunc D θ : PowerSeries F)) :
          PowerSeries F) := (PowerSeries.coeff_coe_trunc_of_lt hr).symm
    _ = PowerSeries.coeff r (PowerSeries.trunc D (P * θ) : PowerSeries F) := by
      rw [PowerSeries.trunc_mul_trunc]
    _ = _ := PowerSeries.coeff_coe_trunc_of_lt hr







end Nodes

end D1Bound5
end
