-- Prove2me | solution 1 for D1Bound5.coherent_three_general_scalar
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:14:03.833973+00:00
-- url     : https://prove2.me/submissions/169388fa-2eb0-478b-b826-18c7c6e23e10

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







/-- Scalar conversion with comfortable rational margins; the stronger
tail envelope above yields `96/35 < 3` for the second contribution. -/
theorem _root_.solution
    (A B S P Q E Z D d L : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hS : 0 < S) (hP : 0 < P) (hQ : 0 < Q)
    (hE : 0 < E) (hZ : 0 < Z) (hd0 : 0 ≤ d)
    (hD : D ≤ 8 * B * S ^ 2) (hEsq : E ^ 2 = P * Q)
    (hZlo : (35 / 36 : ℝ) * E < Z) (hZhi : Z < (37 / 36 : ℝ) * E)
    (hd : d < 36 / (71 * P * Q))
    (hL : L ≤ D * E * (d + (1 / (3 * P ^ 3)) / (A * B * S))) :
    L < 5 * B * S ^ 2 / Z + 3 * S * Z / (A * P ^ 3) := by
  have hfirst : 8 * B * S ^ 2 * E * d < 5 * B * S ^ 2 / Z := by
    have h1 := mul_lt_mul_of_pos_left hd (by positivity : 0 < 8 * B * S ^ 2 * E)
    have heq : 8 * B * S ^ 2 * E * (36 / (71 * P * Q)) =
        288 * B * S ^ 2 / (71 * E) := by
      have hden : 71 * P * Q = 71 * E ^ 2 := by
        rw [mul_assoc, ← hEsq]
      rw [hden]
      field_simp
      ring
    have h2 : 288 * B * S ^ 2 / (71 * E) < 5 * B * S ^ 2 / Z := by
      apply (div_lt_div_iff₀ (by positivity) hZ).2
      have h := mul_lt_mul_of_pos_left hZhi (by positivity : 0 < 288 * B * S ^ 2)
      nlinarith only [h, mul_pos (mul_pos hB (sq_pos_of_pos hS)) hE]
    exact (h1.trans_eq heq).trans h2
  have hsecond : 8 * B * S ^ 2 * E * ((1 / (3 * P ^ 3)) / (A * B * S)) <
      3 * S * Z / (A * P ^ 3) := by
    have heq : 8 * B * S ^ 2 * E * ((1 / (3 * P ^ 3)) / (A * B * S)) =
        8 * S * E / (3 * A * P ^ 3) := by field_simp <;> ring
    rw [heq]
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).2
    have hz : 8 * E < 9 * Z := by linarith
    have h := mul_lt_mul_of_pos_right hz (by positivity : 0 < S * A * P ^ 3)
    nlinarith only [h]
  have hcoarse : L ≤ 8 * B * S ^ 2 * E * d +
      8 * B * S ^ 2 * E * ((1 / (3 * P ^ 3)) / (A * B * S)) := by
    calc
      L ≤ D * E * (d + (1 / (3 * P ^ 3)) / (A * B * S)) := hL
      _ ≤ (8 * B * S ^ 2) * E * (d + (1 / (3 * P ^ 3)) / (A * B * S)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hD hE.le) (by positivity)
      _ = _ := by ring
  exact hcoarse.trans_lt (add_lt_add hfirst hsecond)



end D1Bound5
end
