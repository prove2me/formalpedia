-- Prove2me | solution 1 for D1Bound5.bennettPoleSeries_coeff
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:49:07.306797+00:00
-- url     : https://prove2.me/submissions/6af1e74c-bf21-4a1d-b192-96ddfcfea23c

import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettPoleSeries_Definitions

section
open PowerSeries

namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]



/-- Exact Taylor coefficients of the local reciprocal pole factor. -/
theorem _root_.solution (d : F) (k h : ℕ) :
    PowerSeries.coeff h (bennettPoleSeries d k) =
      Ring.choose (-(k : F)) h * (d⁻¹) ^ (k + h) := by
  simp only [bennettPoleSeries, PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale,
    binomialSeries_coeff, smul_eq_mul, mul_one, pow_add]
  ring





end D1Bound5
end
