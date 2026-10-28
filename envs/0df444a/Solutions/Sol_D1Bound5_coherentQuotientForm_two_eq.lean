-- Prove2me | solution 1 for D1Bound5.coherentQuotientForm_two_eq
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:23:09.465866+00:00
-- url     : https://prove2.me/submissions/11cad994-8ca7-49b6-8d87-fa17d1f3213c

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
import Definitions.Def_D1Bound5_CoherentIntegralForms_Definitions
import Definitions.Def_D1Bound5_CoherentPolynomialWeights_Definitions
import Definitions.Def_D1Bound5_CoherentQuotientForms_Definitions
import Theorems.Thm_D1Bound5_coherentWeights2_eq_quotient

section
open Finset
open scoped NumberField
open Module

namespace D1Bound5

/-- The quotient-weighted two-anchor form is exactly the difference
of its two actual coherent anchor roots and its terminal-root term. -/
theorem _root_.solution
    (a : Fin 2 → ℂ) (hinj : Function.Injective a) (p q eta : ℂ) :
    coherentQuotientForm a (a 0 - a 1) p q eta =
      coherentAnchorRoot (a 0) p q eta - coherentAnchorRoot (a 1) p q eta -
        (a 0 - a 1) * coherentTerminalRoot p q eta := by
  have hw (i : Fin 2) :
      (a 0 - a 1) * a i ^ (2 - 2) /
          (∏ j ∈ Finset.univ.erase i, (a i - a j)) = coherentWeights2 a i := by
    exact (coherentWeights2_eq_quotient a hinj i).symm
  unfold coherentQuotientForm
  simp_rw [hw]
  simp [Fin.sum_univ_two, coherentWeights2]
  ring





end D1Bound5
end
