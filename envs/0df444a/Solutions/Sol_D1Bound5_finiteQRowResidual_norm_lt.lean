-- Prove2me | solution 1 for D1Bound5.finiteQRowResidual_norm_lt
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:24:11.193595+00:00
-- url     : https://prove2.me/submissions/0b08f93a-6c2f-42f1-8846-1651eae4b158

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Int.GCD
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FiniteQMatrix_Definitions
import Definitions.Def_D1Bound5_FiniteQResidualIdentity_Definitions
import Definitions.Def_D1Bound5_FiniteQRowBound_Definitions
import Theorems.Thm_D1Bound5_finiteQResidual_norm_lt

section
namespace D1Bound5





/-- Every one of the actual five rows has the uniform residual bound,
without a premise certifying its formal cancellations. -/
theorem _root_.solution
    (a b s t c : ℂ) (A T : ℝ) (hA : 0 < A)
    (hlower : ∀ j, A ≤ ‖finiteQAnchors a b s t j‖)
    (hupper : ∀ j, ‖finiteQAnchors a b s t j‖ ≤ T)
    (hAC : 1000 ≤ A*‖c‖) (i : Fin 5) :
    ‖finiteQRowResidual a b s t c i‖ < 3*T/(2*A^2*‖c‖^4) := by
  have hab := finiteQResidual_norm_lt a b c A T hA (hlower 0) (hlower 1)
    (hupper 0) (hupper 1) hAC
  have has := finiteQResidual_norm_lt a s c A T hA (hlower 0) (hlower 2)
    (hupper 0) (hupper 2) hAC
  have hbs := finiteQResidual_norm_lt b s c A T hA (hlower 1) (hlower 2)
    (hupper 1) (hupper 2) hAC
  have hat := finiteQResidual_norm_lt a t c A T hA (hlower 0) (hlower 3)
    (hupper 0) (hupper 3) hAC
  have hbt := finiteQResidual_norm_lt b t c A T hA (hlower 1) (hlower 3)
    (hupper 1) (hupper 3) hAC
  fin_cases i
  · simpa [finiteQRowResidual, finiteQDividedMatrix, finiteQAnchors,
      finiteQResidual, Fin.sum_univ_succ, add_assoc] using hab
  · simpa [finiteQRowResidual, finiteQDividedMatrix, finiteQAnchors,
      finiteQResidual, Fin.sum_univ_succ, add_assoc] using has
  · simpa [finiteQRowResidual, finiteQDividedMatrix, finiteQAnchors,
      finiteQResidual, Fin.sum_univ_succ, add_assoc] using hbs
  · simpa [finiteQRowResidual, finiteQDividedMatrix, finiteQAnchors,
      finiteQResidual, Fin.sum_univ_succ, add_assoc] using hat
  · simpa [finiteQRowResidual, finiteQDividedMatrix, finiteQAnchors,
      finiteQResidual, Fin.sum_univ_succ, add_assoc] using hbt





end D1Bound5
end
