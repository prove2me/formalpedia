-- Prove2me | solution 1 for D1Bound5.bennettClearedTaylor_two_poles_scaled_eval
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:24:29.656972+00:00
-- url     : https://prove2.me/submissions/cc35f45b-3784-467f-84c5-b6c337bdb0d4

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettClearedResidues_Definitions
import Definitions.Def_D1Bound5_BennettPoleSeries_Definitions
import Theorems.Thm_D1Bound5_bennettPoleSeries_coeff

section
open Finset

namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]















/-- Expanding the two actual reciprocal-pole series gives a finite sum
with exactly the three Taylor indices used in the manuscript. -/
theorem _root_.solution
    (s ν a N d e : F) (k r p q : ℕ) :
    s * (bennettClearedTaylor k r ν a
      (bennettPoleSeries d p * bennettPoleSeries e q)).eval N =
    ∑ ht ∈ Finset.antidiagonal r, ∑ uv ∈ Finset.antidiagonal ht.2,
      s * ((Ring.choose ((k : F) + ν) ht.1 *
        ((Ring.choose (-(p : F)) uv.1 * (d⁻¹) ^ (p + uv.1)) *
          (Ring.choose (-(q : F)) uv.2 * (e⁻¹) ^ (q + uv.2)))) *
            (N + a) ^ (k - ht.1)) := by
  unfold bennettClearedTaylor
  rw [Polynomial.eval_finsetSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ht hht
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_add, Polynomial.eval_X, PowerSeries.coeff_mul, bennettPoleSeries_coeff]
  rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]













end D1Bound5
end
