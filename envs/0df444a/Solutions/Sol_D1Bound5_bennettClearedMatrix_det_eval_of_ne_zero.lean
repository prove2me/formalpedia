-- Prove2me | solution 1 for D1Bound5.bennettClearedMatrix_det_eval_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:01:48.528191+00:00
-- url     : https://prove2.me/submissions/0e7dafb0-275a-44b5-a361-3781b14703b5

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettClearedResidues_Definitions
import Definitions.Def_D1Bound5_BennettDeterminantConstant_Definitions
import Definitions.Def_D1Bound5_BennettResidualCancellation_Definitions
import Definitions.Def_D1Bound5_BennettResiduePolynomials_Definitions
import Theorems.Thm_D1Bound5_bennettPolynomialMatrix_det_monomial
import Theorems.Thm_D1Bound5_bennettPolynomialResidue_homogenize

section
open Finset

namespace D1Bound5

variable {F I : Type*} [Field F] [CharZero F]
variable [Fintype I] [DecidableEq I]



/-- Homogenization of the actual matrices, with all scalar powers retained. -/
theorem bennettClearedMatrix_eval (a : I → F) (k : ℕ) (ν N : F) (hN : N ≠ 0) :
    (bennettClearedMatrix a k ν).map (Polynomial.evalRingHom N) =
      N ^ k • (bennettPolynomialMatrix a k ν).map (Polynomial.evalRingHom N⁻¹) := by
  ext i j
  exact (bennettPolynomialResidue_homogenize Finset.univ a k ν N i j hN).symm

/-- The determinant of the cleared matrix evaluates to the single coefficient
of the original determinant at every nonzero value of the variable. -/
theorem _root_.solution
    (a : I → F) (ha : Function.Injective a) (k : ℕ) (hk : 1 ≤ k)
    (ν : F) (q : I) (hq : a q = 0) (N : F) (hN : N ≠ 0) :
    (bennettClearedMatrix a k ν).det.eval N =
      (bennettPolynomialMatrix a k ν).det.coeff (Fintype.card I * k) := by
  calc
    _ = ((bennettClearedMatrix a k ν).map (Polynomial.evalRingHom N)).det :=
      (Polynomial.evalRingHom N).map_det _
    _ = (N ^ k) ^ Fintype.card I *
        (bennettPolynomialMatrix a k ν).det.eval N⁻¹ := by
      rw [bennettClearedMatrix_eval a k ν N hN, Matrix.det_smul]
      exact congrArg (fun z : F => (N ^ k) ^ Fintype.card I * z)
        ((Polynomial.evalRingHom N⁻¹).map_det (bennettPolynomialMatrix a k ν)).symm
    _ = (N ^ k) ^ Fintype.card I *
        ((bennettPolynomialMatrix a k ν).det.coeff (Fintype.card I * k) *
          (N⁻¹) ^ (Fintype.card I * k)) := by
      conv_lhs => rw [bennettPolynomialMatrix_det_monomial a ha k hk ν q hq]
      rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    _ = _ := by
      rw [← pow_mul, Nat.mul_comm k (Fintype.card I)]
      calc
        N ^ (Fintype.card I * k) *
            ((bennettPolynomialMatrix a k ν).det.coeff (Fintype.card I * k) *
              (N⁻¹) ^ (Fintype.card I * k)) =
            (bennettPolynomialMatrix a k ν).det.coeff (Fintype.card I * k) *
              (N ^ (Fintype.card I * k) * (N⁻¹) ^ (Fintype.card I * k)) := by ring
        _ = _ := by rw [← mul_pow, mul_inv_cancel₀ hN, one_pow, mul_one]





end D1Bound5
end
