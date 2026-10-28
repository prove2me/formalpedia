-- Prove2me | solution 1 for D1Bound5.bennettPolynomialResidue_residual_tail_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:34:04.764039+00:00
-- url     : https://prove2.me/submissions/4dc05aed-64ac-400b-848b-3aa574f2d1ff

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
import Definitions.Def_D1Bound5_BennettLocalResidues_Definitions
import Definitions.Def_D1Bound5_BennettResiduePolynomials_Definitions
import Theorems.Thm_D1Bound5_bennettPolynomialResidue_residual_coeff_eq_moment
import Theorems.Thm_D1Bound5_bennettPolynomialResidue_residual_coeff_zero
import Theorems.Thm_D1Bound5_bennettPolynomialResidue_residual_hasSum

section
open Finset

namespace D1Bound5





section Nodes

variable {I : Type*} [Fintype I] [DecidableEq I]





/-- After the proved cancellation, the actual analytic residual is exactly
the high-degree residue-moment tail. -/
theorem _root_.solution
    (a : I → ℂ) (ha : Function.Injective a) (k : ℕ) (hk : 1 ≤ k)
    (ν x : ℂ) (i : I) (hx : ∀ j, ‖a j * x‖ < 1) :
    HasSum (fun t : ℕ =>
      (Ring.choose ((k : ℂ) + ν) (Fintype.card I * k + t) *
        ∑ j, bennettLocalResidue a
          (fun l => k + (if i = l then 1 else 0) - 1)
          (Polynomial.X ^ (Fintype.card I * k + t)) j) *
            x ^ (Fintype.card I * k + t))
      (∑ j, (bennettPolynomialResidue univ a k ν i j).eval x *
        (1 + a j * x) ^ ν) := by
  let R : PowerSeries ℂ :=
    ∑ j, (bennettPolynomialResidue univ a k ν i j : PowerSeries ℂ) *
      PowerSeries.rescale (a j) (PowerSeries.binomialSeries ℂ ν)
  have hzero : (∑ r ∈ range (Fintype.card I * k),
      PowerSeries.coeff r R * x ^ r) = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    rw [show PowerSeries.coeff r R = 0 from
      bennettPolynomialResidue_residual_coeff_zero a ha k hk ν i r
        (Finset.mem_range.mp hr), zero_mul]
  have htail : HasSum (fun t : ℕ =>
      PowerSeries.coeff (t + Fintype.card I * k) R * x ^ (t + Fintype.card I * k))
      (∑ j, (bennettPolynomialResidue univ a k ν i j).eval x *
        (1 + a j * x) ^ ν) := by
    apply (hasSum_nat_add_iff
      (f := fun r : ℕ => PowerSeries.coeff r R * x ^ r) (Fintype.card I * k)).mpr
    rw [hzero, add_zero]
    exact bennettPolynomialResidue_residual_hasSum a k ν x i hx
  simpa only [R, Nat.add_comm,
    bennettPolynomialResidue_residual_coeff_eq_moment a k hk ν i] using htail

end Nodes

end D1Bound5
end
