-- Prove2me | solution 1 for D1Bound5.bennettPolynomialResidue_residual_dvd
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:36:06.727377+00:00
-- url     : https://prove2.me/submissions/375327a0-e342-4c00-a975-2d3b22e36310

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
import Definitions.Def_D1Bound5_BennettResiduePolynomials_Definitions
import Theorems.Thm_D1Bound5_bennettPolynomialResidue_residual_coeff_zero
import Theorems.Thm_D1Bound5_bennett_coeff_mul_trunc

section
open Finset

namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]



section Nodes

variable {I : Type*} [Fintype I] [DecidableEq I]





/-- Polynomial form of the actual residual cancellation, suitable for the
column-replacement determinant argument. -/
theorem _root_.solution
    (a : I → F) (ha : Function.Injective a) (k : ℕ) (hk : 1 ≤ k)
    (ν : F) (i : I) :
    (Polynomial.X : Polynomial F) ^ (Fintype.card I * k) ∣
      ∑ j, PowerSeries.trunc (Fintype.card I * k)
        (PowerSeries.rescale (a j) (PowerSeries.binomialSeries F ν)) *
          bennettPolynomialResidue Finset.univ a k ν i j := by
  apply Polynomial.X_pow_dvd_iff.mpr
  intro r hr
  rw [← Polynomial.coeff_coe]
  change PowerSeries.coeff r (Polynomial.coeToPowerSeries.ringHom (∑ j, _)) = 0
  simp only [map_sum, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_mul]
  calc
    _ = ∑ j, PowerSeries.coeff r
        ((bennettPolynomialResidue Finset.univ a k ν i j : PowerSeries F) *
          PowerSeries.rescale (a j) (PowerSeries.binomialSeries F ν)) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [mul_comm]
      exact bennett_coeff_mul_trunc _ _ _ _ hr
    _ = 0 := by
      simpa only [map_sum] using
        bennettPolynomialResidue_residual_coeff_zero a ha k hk ν i r hr





end Nodes

end D1Bound5
end
