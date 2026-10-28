-- Prove2me | solution 1 for D1Bound5.coherent_three_parameter_upper_scalar
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:33:37.967677+00:00
-- url     : https://prove2.me/submissions/18850144-8c27-427b-a419-b6feef0b6ce3

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







/-- Direct parameter estimate from the exact coherent norm identity. -/
theorem _root_.solution
    (V P Q E Z D d F L u lam : ℝ)
    (hV : 0 < V) (hP : 0 < P) (hQ : 0 < Q) (hE : 0 < E)
    (hZ : 0 < Z) (hD : 0 < D) (hu : 0 < u)
    (hEsq : E^2 = P*Q)
    (hZlo : (99/100 : ℝ)*E < Z) (hZhi : Z < (101/100 : ℝ)*E)
    (hd : d < 100/(199*P*Q)) (hF : F ≤ u/P^3)
    (hlam : 100*u/99 < lam) (hL : L ≤ D*E*(d+F/V)) :
    L < 51*D/(100*Z) + lam*D*Z/(V*P^3) := by
  have hfirst : D*E*d < 51*D/(100*Z) := by
    have h1 := mul_lt_mul_of_pos_left hd (mul_pos hD hE)
    have heq : D*E*(100/(199*P*Q)) = 100*D/(199*E) := by
      have hden : 199*P*Q = 199*E^2 := by
        rw [mul_assoc, ← hEsq]
      rw [hden]
      field_simp <;> ring
    have h2 : 100*D/(199*E) < 51*D/(100*Z) := by
      apply (div_lt_div_iff₀ (by positivity) (by positivity)).2
      have h := mul_lt_mul_of_pos_left hZhi (by positivity : 0 < 10000*D)
      nlinarith only [h, mul_pos hD hE]
    exact (h1.trans_eq heq).trans h2
  have hsecond : D*E*(F/V) < lam*D*Z/(V*P^3) := by
    have h1 : D*E*(F/V) ≤ D*u*E/(V*P^3) := by
      calc
        _ ≤ D*E*((u/P^3)/V) := mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right hF hV.le) (by positivity)
        _ = _ := by field_simp <;> ring
    have huE : u*E < lam*Z := by
      have he : E < (100/99 : ℝ)*Z := by linarith only [hZlo]
      have h2 := mul_lt_mul_of_pos_left he hu
      have h3 := mul_lt_mul_of_pos_right hlam hZ
      nlinarith only [h2, h3]
    have h2 : D*u*E/(V*P^3) < lam*D*Z/(V*P^3) := by
      apply div_lt_div_of_pos_right _ (by positivity)
      have h := mul_lt_mul_of_pos_left huE hD
      nlinarith only [h]
    exact h1.trans_lt h2
  have hcoarse : L ≤ D*E*d+D*E*(F/V) := by nlinarith only [hL]
  exact hcoarse.trans_lt (add_lt_add hfirst hsecond)



end D1Bound5
end
