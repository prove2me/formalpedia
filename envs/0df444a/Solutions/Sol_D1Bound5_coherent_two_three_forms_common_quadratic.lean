-- Prove2me | solution 1 for D1Bound5.coherent_two_three_forms_common_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:55:27.113691+00:00
-- url     : https://prove2.me/submissions/5272bee8-1900-45b3-bb47-9fefef873620

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

section
open Finset Polynomial

namespace D1Bound5







/-- Two vanishing coherent triple forms sharing their first two roots
produce one quadratic taking all four prescribed values.  Only the
difference of the two shared anchors is divided out. -/
theorem _root_.solution
    {F : Type*} [Field F] (a R : Fin 4 → F) (z : F) (hab : a 0 ≠ a 1)
    (h2 : -(a 0-a 1)*(a 0-a 2)*(a 1-a 2)*z +
      a 0*(a 1-a 2)*R 0 - a 1*(a 0-a 2)*R 1 + a 2*(a 0-a 1)*R 2 = 0)
    (h3 : -(a 0-a 1)*(a 0-a 3)*(a 1-a 3)*z +
      a 0*(a 1-a 3)*R 0 - a 1*(a 0-a 3)*R 1 + a 3*(a 0-a 1)*R 3 = 0) :
    ∃ v w : F, ∀ i, z * (a i)^2 + v * a i + w = a i * R i := by
  let v := (a 0 * R 0 - a 1 * R 1) / (a 0-a 1) - z * (a 0+a 1)
  let w := a 0*a 1*z + a 0*a 1*(R 1-R 0)/(a 0-a 1)
  refine ⟨v, w, ?_⟩
  intro i
  have hd : a 0-a 1 ≠ 0 := sub_ne_zero.mpr hab
  fin_cases i
  · dsimp [v, w]
    field_simp [hd]
    ring
  · dsimp [v, w]
    field_simp [hd]
    ring
  · dsimp [v, w]
    field_simp [hd]
    linear_combination -h2
  · dsimp [v, w]
    field_simp [hd]
    linear_combination -h3









end D1Bound5
end
