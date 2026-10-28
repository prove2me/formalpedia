-- Prove2me | solution 1 for D1Bound5.bennettNumeratorMajorant_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:32:45.371006+00:00
-- url     : https://prove2.me/submissions/99f9f7d8-36ed-4d24-a933-fcad84fb5445

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettCoefficientMajorant_Definitions

section
open Finset

namespace D1Bound5













/-- The finite numerator majorant has its ordinary polynomial value as sum. -/
theorem _root_.solution (U r : ℝ) (k : ℕ) :
    HasSum (fun h : ℕ => PowerSeries.coeff h (bennettNumeratorMajorant U k) * r ^ h)
      ((U + r) ^ (k + 1) / U) := by
  let P : Polynomial ℝ := Polynomial.C U⁻¹ * (Polynomial.C U + Polynomial.X) ^ (k + 1)
  have hP : (P : PowerSeries ℝ) = bennettNumeratorMajorant U k := by
    simp [P, bennettNumeratorMajorant]
  have hpzero (h : ℕ) (hh : h ∉ P.support) : P.coeff h * r ^ h = 0 := by
    have hcoeff : P.coeff h = 0 := by
      simpa only [Polynomial.mem_support_iff, not_not] using hh
    rw [hcoeff, zero_mul]
  have hp : HasSum (fun h : ℕ => P.coeff h * r ^ h) (P.eval r) := by
    simpa only [Polynomial.eval_eq_sum, Polynomial.sum] using
      (hasSum_sum_of_ne_finset_zero (s := P.support) hpzero)
  have heval : P.eval r = (U + r) ^ (k + 1) / U := by simp [P, div_eq_mul_inv, mul_comm]
  simpa only [← hP, Polynomial.coeff_coe, heval] using hp



end D1Bound5
end
