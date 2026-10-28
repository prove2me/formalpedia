-- Prove2me | solution 1 for D1Bound5.bennettClearedMatrix_det_formula
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:34:03.956906+00:00
-- url     : https://prove2.me/submissions/b458a7b5-5ce0-4b02-90d6-b61461d0cc11

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
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
import Definitions.Def_D1Bound5_BennettDeterminantConstant_Definitions
import Definitions.Def_D1Bound5_BennettDeterminantFormula_Definitions
import Definitions.Def_D1Bound5_BennettResidualCancellation_Definitions
import Theorems.Thm_D1Bound5_bennettClearedMatrix_det_constant
import Theorems.Thm_D1Bound5_bennettClearedMatrix_det_eval_zero_formula

section
open Finset

namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]











/-- The cleared determinant equals the explicit product as a polynomial,
including its value at every possible evaluation point. -/
theorem _root_.solution
    (n : ℕ) (a : Fin (n + 1) → F) (ha : Function.Injective a)
    (k : ℕ) (hk : 1 ≤ k) (ν : F) (h0 : a 0 = 0) :
    (bennettClearedMatrix a k ν).det =
      Polynomial.C (bennettBinomialProduct (n + 1) k ν * bennettDirectedProduct a k) := by
  calc
    _ = Polynomial.C ((bennettClearedMatrix a k ν).det.eval 0) := by
      rw [bennettClearedMatrix_det_constant a ha k hk ν 0 h0]
      simp
    _ = _ := by rw [bennettClearedMatrix_det_eval_zero_formula k hk n a ha ν h0]



end D1Bound5
end
