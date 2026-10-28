-- Prove2me | solution 1 for D1Bound5.bennettTwoClearedMatrix_det_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:43:18.862723+00:00
-- url     : https://prove2.me/submissions/6874b56f-4fee-4300-9b21-0f817ee1214d

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettDeterminantConstant_Definitions
import Definitions.Def_D1Bound5_BennettTwoIntegralEntries_Definitions
import Definitions.Def_D1Bound5_BennettTwoIntegralMatrix_Definitions
import Theorems.Thm_D1Bound5_bennettClearedMatrix_det_half_eval_ne_zero
import Theorems.Thm_D1Bound5_bennettTwoNodes_injective

section
namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]





/-- Nonsingularity of the actual integral two-anchor matrix. All of its
ingredients are constructed explicitly; no determinant certificate is input. -/
theorem _root_.solution
    (a b c : F) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    (k : ℕ) (hk : 1 ≤ k) : (bennettTwoClearedMatrix a b c k).det ≠ 0 := by
  have hnodes := bennettTwoNodes_injective a b ha hb hab
  have hzero : bennettTwoNodes a b 0 = 0 := rfl
  have hdet := bennettClearedMatrix_det_half_eval_ne_zero 2 (bennettTwoNodes a b)
    hnodes k hk hzero (a * b * c)
  have hscale : (4 * a * b * (a - b) ^ 2 : F) ^ k ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) ha) hb)
      (pow_ne_zero _ (sub_ne_zero.mpr hab)))
  have hmatrix : bennettTwoClearedMatrix a b c k =
      (4 * a * b * (a - b) ^ 2 : F) ^ k •
        (bennettClearedMatrix (bennettTwoNodes a b) k (1 / 2 : F)).map
          (Polynomial.evalRingHom (a * b * c)) := by
    apply Matrix.ext
    intro i j
    rfl
  rw [hmatrix, Matrix.det_smul]
  apply mul_ne_zero (pow_ne_zero _ hscale)
  intro hmap
  exact hdet (((Polynomial.evalRingHom (a * b * c)).map_det
    (bennettClearedMatrix (bennettTwoNodes a b) k (1 / 2 : F))).trans hmap)

end D1Bound5
end
