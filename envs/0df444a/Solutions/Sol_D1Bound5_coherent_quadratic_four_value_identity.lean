-- Prove2me | solution 1 for D1Bound5.coherent_quadratic_four_value_identity
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:51:48.172637+00:00
-- url     : https://prove2.me/submissions/ec268745-bdb9-45d8-8f77-4b094e7aa050

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
import Theorems.Thm_D1Bound5_coherent_quadratic_four_value_coefficients

section
open Finset Polynomial

namespace D1Bound5











/-- Eliminating the two lower quadratic coefficients gives the exact
rational identity used in the four-anchor contradiction. -/
theorem _root_.solution
    (a R : Fin 4 → ℂ) (hinj : Function.Injective a) (ha : ∀ i, a i ≠ 0)
    (p q z v w : ℂ) (hz : z^2 = p*q+1)
    (hR : ∀ i, (R i)^2 = (a i*p+1)*(a i*q+1))
    (hJ : ∀ i, z*(a i)^2+v*a i+w = a i*R i) :
    p*q+1 =
      (coherentElementary2 a + 1 -
        (coherentElementary3 a)^2 / (4*coherentElementary4 a))^2 /
          (4*coherentElementary4 a) := by
  obtain ⟨hw, hvw, hvz⟩ := coherent_quadratic_four_value_coefficients a R hinj p q z v w hz hR hJ
  have he4 : coherentElementary4 a ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (ha 0) (ha 1)) (ha 2)) (ha 3)
  have h4e : 4*coherentElementary4 a ≠ 0 := mul_ne_zero (by norm_num) he4
  have hv : v^2 = (coherentElementary3 a)^2 / (4*coherentElementary4 a) := by
    apply (eq_div_iff h4e).2
    linear_combination (2*v*w-coherentElementary3 a) * hvw - 4*v^2 * hw
  rw [← hv, ← hz]
  apply (eq_div_iff h4e).2
  linear_combination
    (2*z*w + (coherentElementary2 a+1-v^2)) * hvz - 4*z^2 * hw





end D1Bound5
end
