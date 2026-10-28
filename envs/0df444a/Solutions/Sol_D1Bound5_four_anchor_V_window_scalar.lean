-- Prove2me | solution 1 for D1Bound5.four_anchor_V_window_scalar
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:33:36.716684+00:00
-- url     : https://prove2.me/submissions/93c09ab0-04c2-4819-b8c6-58547b904b02

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
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Theorems.Thm_D1Bound5_finite_closed_window_incompatible

section
open Finset
open scoped NumberField
open Module

namespace D1Bound5

/-- A convenient smaller closed V window, with rational coefficients
101 and 2/5. The strict actual form estimate excludes its endpoints. -/
theorem _root_.solution
    (A B T P Q Z : ℝ) (hA : 0 < A) (hB : 0 < B) (hT : 0 < T)
    (hP : 0 < P) (hZ : 0 < Z)
    (hlo : (1-1/4000 : ℝ)*P*Q ≤ Z^2)
    (hhi : Z^2 ≤ (1+1/4000 : ℝ)*P*Q)
    (hform : 1 < 5*B*T^2/Z+3*T*Z/(4*A*P^3)) :
    Q < 101*B^2*T^4/P ∨ (2/5 : ℝ)*A^2*P^5/T^2 < Q := by
  by_contra hbad
  push_neg at hbad
  have hlow : 4*(5*B*T^2)^2/(P*(1-1/4000)) ≤ Q := by
    apply le_trans _ hbad.1
    apply (div_le_div_iff₀ (by positivity) hP).2
    have hh : 0 ≤ B^2*T^4*P := by positivity
    nlinarith only [hh]
  have hupp : Q ≤ 1/(4*(3*T/(4*A*P^3))^2*P*(1+1/4000)) := by
    apply le_trans hbad.2
    have heq : 1/(4*(3*T/(4*A*P^3))^2*P*(1+1/4000)) =
        (16000/36009 : ℝ)*A^2*P^5/T^2 := by field_simp; ring
    rw [heq]
    have hp : 0 ≤ A^2*P^5/T^2 := by positivity
    calc
      (2/5 : ℝ)*A^2*P^5/T^2 = (2/5 : ℝ)*(A^2*P^5/T^2) := by ring
      _ ≤ (16000/36009 : ℝ)*(A^2*P^5/T^2) :=
        mul_le_mul_of_nonneg_right (by norm_num) hp
      _ = _ := by ring
  exact finite_closed_window_incompatible P Q Z (5*B*T^2) (3*T/(4*A*P^3))
    (1/4000) hP hZ (by positivity) (by positivity) (by norm_num) (by norm_num)
    hlo hhi (by convert hform using 1 <;> ring) hlow hupp



end D1Bound5
end
