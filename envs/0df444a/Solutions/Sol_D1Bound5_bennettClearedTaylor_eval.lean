-- Prove2me | solution 1 for D1Bound5.bennettClearedTaylor_eval
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:57:30.04175+00:00
-- url     : https://prove2.me/submissions/faa49ee8-6fa3-4bc9-9d45-81dfc4364808

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettClearedResidues_Definitions

section
open Finset

namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]





/-- Evaluation away from the local origin is a single exact coefficient of
the rescaled binomial series times the remaining reciprocal poles. -/
theorem _root_.solution (k r : ℕ) (hr : r ≤ k) (ν a N : F)
    (B : PowerSeries F) (hd : N + a ≠ 0) :
    (bennettClearedTaylor k r ν a B).eval N =
      (N + a) ^ k * PowerSeries.coeff r
        (PowerSeries.rescale (N + a)⁻¹
          (PowerSeries.binomialSeries F ((k : F) + ν)) * B) := by
  unfold bennettClearedTaylor
  rw [Polynomial.eval_finsetSum, PowerSeries.coeff_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ht hht
  have hsum := Finset.mem_antidiagonal.mp hht
  have hh : ht.1 ≤ k := by omega
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_add, Polynomial.eval_X, PowerSeries.coeff_rescale,
    PowerSeries.binomialSeries_coeff, smul_eq_mul, mul_one]
  rw [pow_sub₀ (N + a) hd hh, inv_pow]
  ring



section Nodes

variable {I : Type*} [DecidableEq I]

















end Nodes

end D1Bound5
end
