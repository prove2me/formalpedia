-- Prove2me | solution 1 for D1Bound5.coherent_two_upper_scalar
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:22:09.29873+00:00
-- url     : https://prove2.me/submissions/895c7edc-b35b-4616-8a83-304c7cd6b35b

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

namespace D1Bound5







/-- A scalar conversion of the exact coherent estimate to the two
explicit terms in the manuscript. -/
theorem _root_.solution
    (A B P Q E Z D d F L : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hP : 0 < P) (hQ : 0 < Q)
    (hE : 0 < E) (hZ : 0 < Z) (hD0 : 0 ≤ D) (hd0 : 0 ≤ d) (hF0 : 0 ≤ F)
    (hD : D ≤ 2 * B) (hEsq : E ^ 2 = P * Q)
    (hZlo : (99 / 100 : ℝ) * E < Z) (hZhi : Z < (101 / 100 : ℝ) * E)
    (hd : d < 100 / (199 * P * Q)) (hF : F ≤ 7 / (32 * P ^ 2))
    (hL : L ≤ D * E * (d + F / (A * B))) :
    L < 21 * B / (20 * Z) + Z / (2 * A * P ^ 2) := by
  have hfirst : 2 * B * E * d < 21 * B / (20 * Z) := by
    have h1 : 2 * B * E * d < 2 * B * E * (100 / (199 * P * Q)) :=
      mul_lt_mul_of_pos_left hd (by positivity)
    have heq : 2 * B * E * (100 / (199 * P * Q)) = 200 * B / (199 * E) := by
      rw [mul_assoc 199 P Q, ← hEsq]
      field_simp <;> ring
    have h2 : 200 * B / (199 * E) < 21 * B / (20 * Z) := by
      apply (div_lt_div_iff₀ (by positivity) (by positivity)).2
      have h := mul_lt_mul_of_pos_left hZhi (by positivity : 0 < 4000 * B)
      nlinarith only [h, mul_pos hB hE]
    exact (h1.trans_eq heq).trans h2
  have hsecond : 2 * B * E * (F / (A * B)) < Z / (2 * A * P ^ 2) := by
    have h1 : 2 * B * E * (F / (A * B)) ≤
        2 * B * E * ((7 / (32 * P ^ 2)) / (A * B)) := by
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hF (by positivity)) (by positivity)
    have heq : 2 * B * E * ((7 / (32 * P ^ 2)) / (A * B)) =
        7 * E / (16 * A * P ^ 2) := by field_simp; ring
    have h2 : 7 * E / (16 * A * P ^ 2) < Z / (2 * A * P ^ 2) := by
      apply (div_lt_div_iff₀ (by positivity) (by positivity)).2
      have hz : 7 * E < 8 * Z := by linarith
      have h := mul_lt_mul_of_pos_right hz (by positivity : 0 < 2 * A * P ^ 2)
      nlinarith only [h]
    exact (h1.trans_eq heq).trans_lt h2
  have hcoarse : L ≤ 2 * B * E * d + 2 * B * E * (F / (A * B)) := by
    calc
      L ≤ D * E * (d + F / (A * B)) := hL
      _ ≤ (2 * B) * E * (d + F / (A * B)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hD hE.le) (by positivity)
      _ = _ := by ring
  exact hcoarse.trans_lt (add_lt_add hfirst hsecond)



end D1Bound5
end
