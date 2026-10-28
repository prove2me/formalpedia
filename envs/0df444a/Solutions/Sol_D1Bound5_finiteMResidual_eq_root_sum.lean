-- Prove2me | solution 1 for D1Bound5.finiteMResidual_eq_root_sum
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:57:36.887454+00:00
-- url     : https://prove2.me/submissions/03322db5-d641-44f6-b86f-f6b3037b0114

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Real
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
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FiniteMBennettIdentity_Definitions
import Definitions.Def_D1Bound5_FiniteMMatrix_Definitions
import Definitions.Def_D1Bound5_FiniteMResidualPoint_Definitions
import Definitions.Def_D1Bound5_FiniteMRowBound_Definitions

section
namespace D1Bound5



theorem _root_.solution (a b s c : ℂ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hs : s ≠ 0) (hc : c ≠ 0) (i : Fin 4) :
    finiteMResidual a b s c i = finiteMDividedMatrix a b s c i 0+
      ∑ j : Fin 3, finiteMAnchors a b s j*finiteMDividedMatrix a b s c i j.succ*
        (1+1/(finiteMAnchors a b s j*c))^(1/2 : ℂ) := by
  have hnode (j : Fin 3) : finiteMNodes a b s j.succ*(a*b*s*c)⁻¹ =
      1/(finiteMAnchors a b s j*c) := by
    have hcases : ∀ j : Fin 3, j = 0 ∨ j = 1 ∨ j = 2 := by decide
    rcases hcases j with rfl | rfl | rfl
    · change (b*s)*(a*b*s*c)⁻¹ = 1/(a*c)
      field_simp [ha,hb,hs,hc]
      <;> ring
    · change (a*s)*(a*b*s*c)⁻¹ = 1/(b*c)
      field_simp [ha,hb,hs,hc]
      <;> ring
    · change (a*b)*(a*b*s*c)⁻¹ = 1/(s*c)
      field_simp [ha,hb,hs,hc]
      <;> ring
  have hcol (j : Fin 3) : finiteMMatrix a b s c i j.succ =
      finiteMDividedMatrix a b s c i j.succ*finiteMAnchors a b s j := by
    fin_cases j <;> simp [finiteMMatrix,Matrix.mul_diagonal,finiteMAnchors]
  unfold finiteMResidual
  rw [Fin.sum_univ_succ]
  have hfirst : finiteMMatrix a b s c i 0*
      (1+finiteMNodes a b s 0*(a*b*s*c)⁻¹)^(1/2 : ℂ) = finiteMDividedMatrix a b s c i 0 := by
    simp [finiteMMatrix,Matrix.mul_diagonal,finiteMNodes]
  rw [hfirst]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [hnode,hcol]
  ring





end D1Bound5
end
