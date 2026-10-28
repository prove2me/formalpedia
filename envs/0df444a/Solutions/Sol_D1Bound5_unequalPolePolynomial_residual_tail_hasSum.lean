-- Prove2me | solution 1 for D1Bound5.unequalPolePolynomial_residual_tail_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:23:22.705015+00:00
-- url     : https://prove2.me/submissions/102e11fe-1574-4982-8b19-46c151d0e93f

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettLocalResidues_Definitions
import Definitions.Def_D1Bound5_UnequalPoleResidual_Definitions
import Theorems.Thm_D1Bound5_unequalPolePolynomial_residual_coeff
import Theorems.Thm_D1Bound5_unequalPolePolynomial_residual_coeff_zero
import Theorems.Thm_D1Bound5_unequalPolePolynomial_residual_hasSum

section
open Finset

namespace D1Bound5

variable {I : Type*} [Fintype I] [DecidableEq I]









theorem _root_.solution
    (a : I → ℂ) (ha : Function.Injective a) (e : I → ℕ)
    (k : ℕ) (he : ∀ j, e j ≤ k) (ν x : ℂ)
    (hx : ∀ j, ‖a j*x‖ < 1) :
    HasSum (fun t : ℕ =>
      (Ring.choose ((k : ℂ)+ν) ((∑ j,(e j+1))-1+t) *
        ∑ j, bennettLocalResidue a e
          (Polynomial.X^((∑ j,(e j+1))-1+t)) j)*
            x^((∑ j,(e j+1))-1+t))
      (∑ j, (unequalPolePolynomial a e k ν j).eval x*(1+a j*x)^ν) := by
  let D : ℕ := (∑ j,(e j+1))-1
  let R : PowerSeries ℂ :=
    ∑ j, (unequalPolePolynomial a e k ν j : PowerSeries ℂ)*
      PowerSeries.rescale (a j) (PowerSeries.binomialSeries ℂ ν)
  have hzero : (∑ r ∈ range D, PowerSeries.coeff r R*x^r) = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    rw [show PowerSeries.coeff r R = 0 from
      unequalPolePolynomial_residual_coeff_zero a ha e k he ν r
        (Finset.mem_range.mp hr),zero_mul]
  have htail : HasSum (fun t : ℕ => PowerSeries.coeff (t+D) R*x^(t+D))
      (∑ j, (unequalPolePolynomial a e k ν j).eval x*(1+a j*x)^ν) := by
    apply (hasSum_nat_add_iff
      (f := fun r : ℕ => PowerSeries.coeff r R*x^r) D).mpr
    rw [hzero,add_zero]
    exact unequalPolePolynomial_residual_hasSum a e k ν x hx
  simpa only [R,D,Nat.add_comm,unequalPolePolynomial_residual_coeff a e k he ν] using htail



end D1Bound5
end
