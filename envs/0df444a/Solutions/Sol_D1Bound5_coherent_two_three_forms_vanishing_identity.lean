-- Prove2me | solution 1 for D1Bound5.coherent_two_three_forms_vanishing_identity
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:37:38.894424+00:00
-- url     : https://prove2.me/submissions/26d6bc94-ed53-4289-aa2b-e3dd6f37da33

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
import Definitions.Def_D1Bound5_CoherentThreeSimultaneous_Definitions
import Theorems.Thm_D1Bound5_coherent_quadratic_four_value_identity
import Theorems.Thm_D1Bound5_coherent_two_three_forms_common_quadratic

section
open Finset Polynomial

namespace D1Bound5













/-- Simultaneous vanishing forces the manuscript's exact rational
identity, without assuming an interpolating polynomial exists. -/
theorem _root_.solution
    (a R : Fin 4 → ℂ) (hinj : Function.Injective a) (ha : ∀ i, a i ≠ 0)
    (p q z : ℂ) (hz : z^2 = p*q+1)
    (hR : ∀ i, (R i)^2 = (a i*p+1)*(a i*q+1))
    (h2 : -(a 0-a 1)*(a 0-a 2)*(a 1-a 2)*z +
      a 0*(a 1-a 2)*R 0 - a 1*(a 0-a 2)*R 1 + a 2*(a 0-a 1)*R 2 = 0)
    (h3 : -(a 0-a 1)*(a 0-a 3)*(a 1-a 3)*z +
      a 0*(a 1-a 3)*R 0 - a 1*(a 0-a 3)*R 1 + a 3*(a 0-a 1)*R 3 = 0) :
    p*q+1 =
      (coherentElementary2 a + 1 -
        (coherentElementary3 a)^2 / (4*coherentElementary4 a))^2 /
          (4*coherentElementary4 a) := by
  obtain ⟨v,w,hJ⟩ := coherent_two_three_forms_common_quadratic a R z
    (hinj.ne (by decide)) h2 h3
  exact coherent_quadratic_four_value_identity a R hinj ha p q z v w hz hR hJ



end D1Bound5
end
