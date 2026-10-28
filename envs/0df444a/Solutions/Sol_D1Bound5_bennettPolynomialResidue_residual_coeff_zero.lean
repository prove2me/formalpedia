-- Prove2me | solution 1 for D1Bound5.bennettPolynomialResidue_residual_coeff_zero
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:37:50.536979+00:00
-- url     : https://prove2.me/submissions/8ec8fe57-1eb2-4d47-8f88-1f77fc1b39b2

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettClearedResidues_Definitions
import Definitions.Def_D1Bound5_BennettLocalResidues_Definitions
import Definitions.Def_D1Bound5_BennettPoleSeries_Definitions
import Definitions.Def_D1Bound5_BennettResiduePolynomials_Definitions
import Theorems.Thm_D1Bound5_bennettLocalResidue_sum_eq_zero
import Theorems.Thm_D1Bound5_bennettResidueTaylor_coeff_mul_binomial

section
open Finset

namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]



section Nodes

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The genuine Bennett residual has a zero of order at least `card I * k`.
The cancellation is deduced from exact partial fractions, not assumed. -/
theorem _root_.solution
    (a : I → F) (ha : Function.Injective a) (k : ℕ) (hk : 1 ≤ k)
    (ν : F) (i : I) (r : ℕ) (hr : r < Fintype.card I * k) :
    PowerSeries.coeff r
      (∑ j, (bennettPolynomialResidue Finset.univ a k ν i j : PowerSeries F) *
        PowerSeries.rescale (a j) (PowerSeries.binomialSeries F ν)) = 0 := by
  let e : I → ℕ := fun l ↦ k + (if i = l then 1 else 0) - 1
  have he (l : I) : e l + 1 = k + (if i = l then 1 else 0) := by
    dsimp [e]
    split_ifs <;> omega
  have he_le (j : I) : e j ≤ k := by
    dsimp [e]
    split_ifs <;> omega
  have htotal : (∑ l, (e l + 1)) - 1 = Fintype.card I * k := by
    simp_rw [he]
    rw [Finset.sum_add_distrib]
    simp
  have hdeg : (Polynomial.X ^ r : Polynomial F).degree <
      ((∑ l, (e l + 1)) - 1 : ℕ) := by
    rw [Polynomial.degree_X_pow, htotal]
    exact WithBot.coe_lt_coe.mpr hr
  have hzero := bennettLocalResidue_sum_eq_zero a ha e (Polynomial.X ^ r) hdeg
  have hB (j : I) : bennettOtherPoles Finset.univ a k i j =
      bennettLocalReciprocal a e j := by
    unfold bennettOtherPoles bennettLocalReciprocal
    simp_rw [he]
  have hshift (j : I) :
      bennettShiftToSeries (a j) (Polynomial.X ^ r) =
        (PowerSeries.C (a j) + PowerSeries.X) ^ r := by
    simp [bennettShiftToSeries]
  rw [map_sum]
  calc
    _ = Ring.choose ((k : F) + ν) r *
        ∑ j, bennettLocalResidue a e (Polynomial.X ^ r) j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      change PowerSeries.coeff r
        ((bennettResidueTaylor k (e j) ν (a j)
          (bennettOtherPoles Finset.univ a k i j) : PowerSeries F) *
            PowerSeries.rescale (a j) (PowerSeries.binomialSeries F ν)) = _
      rw [bennettResidueTaylor_coeff_mul_binomial k (e j) r (he_le j)]
      simp only [bennettLocalResidue, hshift, hB]
    _ = 0 := by rw [hzero, mul_zero]









end Nodes

end D1Bound5
end
