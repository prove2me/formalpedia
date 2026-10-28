-- Prove2me | solution 1 for D1Bound5.coherent_two_strong_gap_scalar
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:49:43.0618+00:00
-- url     : https://prove2.me/submissions/38611b09-b981-462d-846b-3cf80e6d6d81

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Int.GCD
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

section
open Finset
open scoped NumberField
open Module

namespace D1Bound5



/-- The quantitative two-anchor gap after the analytic upper bound
and integral lower bound have been supplied.  The root-size inputs are
only the elementary consequences of `z^2=pq+1`. -/
theorem _root_.solution
    (A B P Q Z : ℝ) (hA : 1 ≤ A) (hB : 3 ≤ B) (hP : 5 * B ≤ P)
    (hAP : 32 ≤ A * P) (hQ : 5 * A * B * P ≤ Q)
    (hPQ : 10000 < P * Q) (hZ : 0 ≤ Z)
    (hZlower : P * Q - 1 ≤ Z ^ 2) (hZupper : Z ^ 2 ≤ P * Q + 1)
    (hbound : 1 < 21 * B / (20 * Z) + Z / (2 * A * P ^ 2)) :
    A ^ 2 * P ^ 3 < (10001 / 10000 : ℝ) * Q := by
  have hA0 : 0 < A := by linarith
  have hB0 : 0 < B := by linarith
  have hP0 : 0 < P := by linarith
  have hAP0 : 0 < A * P := by positivity
  have hBP : B ^ 2 ≤ B * P := by
    have h := mul_le_mul_of_nonneg_left (show B ≤ P by linarith) hB0.le
    nlinarith only [h]
  have hPQlower : 5 * (A * P) * B ^ 2 ≤ P * Q := by
    have h1 := mul_le_mul_of_nonneg_left hBP (by positivity : 0 ≤ 5 * (A * P))
    have h2 := mul_le_mul_of_nonneg_left hQ hP0.le
    nlinarith only [h1, h2]
  have h160 : 160 * B ^ 2 ≤ 5 * (A * P) * B ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hAP (by positivity : 0 ≤ 5 * B ^ 2)
    nlinarith only [h]
  have hBsq : 9 ≤ B ^ 2 := by nlinarith only [hB, sq_nonneg (B-3)]
  have hZsq : (3 * B) ^ 2 < Z ^ 2 := by
    nlinarith only [hZlower, hPQlower, h160, hBsq]
  have hZ3 : 3 * B < Z := (sq_lt_sq₀ (by positivity) hZ).mp hZsq
  have hZ0 : 0 < Z := by linarith
  have hfirst : 21 * B / (20 * Z) < (1 / 2 : ℝ) := by
    apply (div_lt_iff₀ (by positivity)).2
    nlinarith only [hZ3, hB0]
  have hsecond : (1 / 2 : ℝ) < Z / (2 * A * P ^ 2) := by
    linarith only [hbound, hfirst]
  have hZgap : A * P ^ 2 < Z := by
    have h := (lt_div_iff₀ (by positivity : 0 < 2 * A * P ^ 2)).mp hsecond
    nlinarith only [h]
  have hsquare : (A * P ^ 2) ^ 2 < Z ^ 2 :=
    (sq_lt_sq₀ (by positivity) hZ).mpr hZgap
  have hPQupper : P * Q + 1 < (10001 / 10000 : ℝ) * (P * Q) := by
    nlinarith only [hPQ]
  apply (mul_lt_mul_iff_of_pos_right hP0).mp
  nlinarith only [hsquare, hZupper, hPQupper]



end D1Bound5
end
