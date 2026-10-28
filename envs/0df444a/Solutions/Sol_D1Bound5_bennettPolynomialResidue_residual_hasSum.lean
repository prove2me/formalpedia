-- Prove2me | solution 1 for D1Bound5.bennettPolynomialResidue_residual_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:34:33.131612+00:00
-- url     : https://prove2.me/submissions/107e0e43-1190-427a-ae42-4257ab72499e

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettResiduePolynomials_Definitions
import Theorems.Thm_D1Bound5_bennett_polynomial_series_hasSum
import Theorems.Thm_D1Bound5_bennett_rescaled_binomial_hasSum

section
open Finset

namespace D1Bound5





section Nodes

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The actual finite row of residue polynomials times the complex powers is
the sum of its actual formal coefficients. No residual identity is assumed. -/
theorem _root_.solution
    (a : I → ℂ) (k : ℕ) (ν x : ℂ) (i : I)
    (hx : ∀ j, ‖a j * x‖ < 1) :
    HasSum (fun r : ℕ => PowerSeries.coeff r
      (∑ j, (bennettPolynomialResidue univ a k ν i j : PowerSeries ℂ) *
        PowerSeries.rescale (a j) (PowerSeries.binomialSeries ℂ ν)) * x ^ r)
      (∑ j, (bennettPolynomialResidue univ a k ν i j).eval x *
        (1 + a j * x) ^ ν) := by
  have hh (j : I) : HasSum (fun r : ℕ => PowerSeries.coeff r
      ((bennettPolynomialResidue univ a k ν i j : PowerSeries ℂ) *
        PowerSeries.rescale (a j) (PowerSeries.binomialSeries ℂ ν)) * x ^ r)
      ((bennettPolynomialResidue univ a k ν i j).eval x * (1 + a j * x) ^ ν) := by
    obtain ⟨hs, hn⟩ := bennett_rescaled_binomial_hasSum (a j) ν x (hx j)
    exact bennett_polynomial_series_hasSum _ _ _ _ hs hn
  simpa only [map_sum, Finset.sum_mul] using
    (hasSum_sum (s := (univ : Finset I)) (fun j _ => hh j))





end Nodes

end D1Bound5
end
