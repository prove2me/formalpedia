-- Prove2me | solution 1 for D1Bound5.three_general_window_scalar
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:58:23.725631+00:00
-- url     : https://prove2.me/submissions/6afef254-c596-4779-af05-cadbc25efcc7

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

/-- Closed general-three forbidden interval, with slightly weaker
rational endpoints so that all root errors are absorbed. -/
theorem _root_.solution
    (A B S P Q Z : ℝ) (hA : 0 < A) (hB : 0 < B) (hS : 0 < S)
    (hP : 0 < P) (hZ : 0 < Z)
    (hlo : (1-1/4000 : ℝ)*P*Q ≤ Z^2)
    (hhi : Z^2 ≤ (1+1/4000 : ℝ)*P*Q)
    (hform : 1 < 5*B*S^2/Z+3*S*Z/(A*P^3)) :
    Q < 101*B^2*S^4/P ∨ A^2*P^5/(37*S^2) < Q := by
  by_contra hbad
  push_neg at hbad
  have hlow : 4*(5*B*S^2)^2/(P*(1-1/4000)) ≤ Q := by
    apply le_trans _ hbad.1
    apply (div_le_div_iff₀ (by positivity) hP).2
    have hh : 0 ≤ B^2*S^4*P := by positivity
    nlinarith only [hh]
  have hupp : Q ≤ 1/(4*(3*S/(A*P^3))^2*P*(1+1/4000)) := by
    apply le_trans hbad.2
    have heq : 1/(4*(3*S/(A*P^3))^2*P*(1+1/4000)) =
        (1000/36009 : ℝ)*A^2*P^5/S^2 := by field_simp; ring
    rw [heq]
    have hp : 0 ≤ A^2*P^5/S^2 := by positivity
    have heq' : A^2*P^5/(37*S^2) = (1/37 : ℝ)*(A^2*P^5/S^2) := by ring
    rw [heq']
    calc
      (1/37 : ℝ)*(A^2*P^5/S^2) ≤ (1000/36009 : ℝ)*(A^2*P^5/S^2) :=
        mul_le_mul_of_nonneg_right (by norm_num) hp
      _ = _ := by ring
  exact finite_closed_window_incompatible P Q Z (5*B*S^2) (3*S/(A*P^3))
    (1/4000) hP hZ (by positivity) (by positivity) (by norm_num) (by norm_num)
    hlo hhi (by convert hform using 1 <;> ring) hlow hupp



end D1Bound5
end
