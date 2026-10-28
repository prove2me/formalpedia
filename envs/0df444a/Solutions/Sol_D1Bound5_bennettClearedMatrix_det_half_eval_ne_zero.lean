-- Prove2me | solution 1 for D1Bound5.bennettClearedMatrix_det_half_eval_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:54:22.050917+00:00
-- url     : https://prove2.me/submissions/c237d940-f6c4-4d03-853a-d70797a8e4dc

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
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettDeterminantConstant_Definitions
import Definitions.Def_D1Bound5_BennettDeterminantFormula_Definitions
import Theorems.Thm_D1Bound5_bennettChoose_ne_zero_of_avoids_naturals
import Theorems.Thm_D1Bound5_bennettClearedMatrix_det_formula
import Theorems.Thm_D1Bound5_bennettDirectedProduct_ne_zero
import Theorems.Thm_D1Bound5_bennett_halfInteger_ne_nat

section
open Polynomial

namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]





/-- The concrete generalized choose factors never vanish at nu=1/2,
including every shifted parameter nu-v*k and k=0. -/
theorem bennett_halfInteger_choose_ne_zero (k v : ℕ) :
    Ring.choose ((k : F) + (1 / 2 : F) - (v : F) * (k : F)) k ≠ 0 := by
  apply bennettChoose_ne_zero_of_avoids_naturals
  intro j _
  exact bennett_halfInteger_ne_nat k v j

end D1Bound5
end

section
open Finset

namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]

/-- None of the binomial factors in the actual nu=1/2 determinant vanishes. -/
theorem bennettBinomialProduct_half_ne_zero (n k : ℕ) :
    bennettBinomialProduct n k (1 / 2 : F) ≠ 0 := by
  unfold bennettBinomialProduct
  apply Finset.prod_ne_zero_iff.mpr
  intro v hv
  exact bennett_halfInteger_choose_ne_zero k v



/-- The actual cleared Bennett matrix is nonsingular at every specialization,
for every positive order and every number of distinct nodes containing zero. -/
theorem _root_.solution
    (n : ℕ) (a : Fin (n + 1) → F) (ha : Function.Injective a)
    (k : ℕ) (hk : 1 ≤ k) (h0 : a 0 = 0) (N : F) :
    (bennettClearedMatrix a k (1 / 2 : F)).det.eval N ≠ 0 := by
  rw [bennettClearedMatrix_det_formula n a ha k hk (1 / 2 : F) h0,
    Polynomial.eval_C]
  exact mul_ne_zero (bennettBinomialProduct_half_ne_zero (n + 1) k)
    (bennettDirectedProduct_ne_zero a ha k)



end D1Bound5
end
