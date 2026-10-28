-- Prove2me | solution 1 for D1Bound5.coherentQuotientForm_three_eq
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:21:36.731917+00:00
-- url     : https://prove2.me/submissions/f5bab7c6-f2a2-4792-9a67-2b3d82e7011e

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
import Definitions.Def_D1Bound5_CoherentIntegralForms_Definitions
import Definitions.Def_D1Bound5_CoherentPolynomialWeights_Definitions
import Definitions.Def_D1Bound5_CoherentQuotientForms_Definitions
import Theorems.Thm_D1Bound5_coherentWeights3_eq_quotient

section
open Finset Polynomial

namespace D1Bound5















/-- The quotient expression has exactly the integral polynomial
weights used in the common-quadratic argument. -/
theorem _root_.solution
    (a : Fin 3 → ℂ) (hinj : Function.Injective a) (p q eta : ℂ) :
    coherentQuotientForm a (coherentVandermonde3 a) p q eta =
      -(a 0-a 1)*(a 0-a 2)*(a 1-a 2)*coherentTerminalRoot p q eta +
        a 0*(a 1-a 2)*coherentAnchorRoot (a 0) p q eta -
        a 1*(a 0-a 2)*coherentAnchorRoot (a 1) p q eta +
        a 2*(a 0-a 1)*coherentAnchorRoot (a 2) p q eta := by
  have hw (i : Fin 3) :
      coherentVandermonde3 a * a i ^ (3 - 2) /
        (∏ j ∈ Finset.univ.erase i, (a i-a j)) = coherentWeights3 a i :=
    (coherentWeights3_eq_quotient a hinj i).symm
  unfold coherentQuotientForm
  simp_rw [hw]
  simp [Fin.sum_univ_succ, coherentWeights3, coherentVandermonde3]
  ring

end D1Bound5
end
