-- Prove2me | solution 1 for D1Bound5.bennettPolynomialResidue_residual_coeff_eq_moment
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:34:32.2019+00:00
-- url     : https://prove2.me/submissions/29f62cd8-11d1-439f-b816-2f8c6fa30b13

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
import Definitions.Def_D1Bound5_BennettClearedResidues_Definitions
import Definitions.Def_D1Bound5_BennettLocalResidues_Definitions
import Definitions.Def_D1Bound5_BennettPoleSeries_Definitions
import Definitions.Def_D1Bound5_BennettResiduePolynomials_Definitions
import Theorems.Thm_D1Bound5_bennettResidueTaylor_coeff_mul_binomial

section
open Finset

namespace D1Bound5





section Nodes

variable {I : Type*} [Fintype I] [DecidableEq I]



/-- Arbitrary coefficients of the genuine residual are local residue moments.
This extends the low-degree cancellation identity to the high-degree tail. -/
theorem _root_.solution
    {F : Type*} [Field F] [CharZero F]
    (a : I → F) (k : ℕ) (hk : 1 ≤ k) (ν : F) (i : I) (r : ℕ) :
    PowerSeries.coeff r
      (∑ j, (bennettPolynomialResidue univ a k ν i j : PowerSeries F) *
        PowerSeries.rescale (a j) (PowerSeries.binomialSeries F ν)) =
      Ring.choose ((k : F) + ν) r *
        ∑ j, bennettLocalResidue a
          (fun l => k + (if i = l then 1 else 0) - 1) (Polynomial.X ^ r) j := by
  let e : I → ℕ := fun l => k + (if i = l then 1 else 0) - 1
  have he (l : I) : e l + 1 = k + (if i = l then 1 else 0) := by
    dsimp [e]
    split_ifs <;> omega
  have he_le (j : I) : e j ≤ k := by
    dsimp [e]
    split_ifs <;> omega
  have hB (j : I) : bennettOtherPoles univ a k i j =
      bennettLocalReciprocal a e j := by
    unfold bennettOtherPoles bennettLocalReciprocal
    simp_rw [he]
  have hshift (j : I) :
      bennettShiftToSeries (a j) (Polynomial.X ^ r) =
        (PowerSeries.C (a j) + PowerSeries.X) ^ r := by
    simp [bennettShiftToSeries]
  rw [map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  change PowerSeries.coeff r
    ((bennettResidueTaylor k (e j) ν (a j)
      (bennettOtherPoles univ a k i j) : PowerSeries F) *
        PowerSeries.rescale (a j) (PowerSeries.binomialSeries F ν)) = _
  rw [bennettResidueTaylor_coeff_mul_binomial k (e j) r (he_le j)]
  simp only [bennettLocalResidue, hshift, hB, e]



end Nodes

end D1Bound5
end
