-- Prove2me | solution 1 for D1Bound5.productFive_compressed_entry
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:21:14.662979+00:00
-- url     : https://prove2.me/submissions/af54b5ff-365a-40e4-921c-7212206c6bfe

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_ProductFiveRankTwo_Definitions

section
open Matrix

namespace D1Bound5











/-- All four entries of the two-by-two compressed correction. Its
two mixed bilinear terms are deliberately kept distinct, so this lemma
does not assume that the inverse matrix is symmetric. -/
theorem _root_.solution
    (X : Matrix (Fin 4) (Fin 4) ℂ)
    (f w : Fin 4 → ℂ) (d : ℂ) (i j : Fin 2) :
    (productFiveRows f w d * X * productFiveColumns f w) i j =
      if i = 0 then
        (if j = 0 then
          -(w ⬝ᵥ (X *ᵥ f)) / d - (f ⬝ᵥ (X *ᵥ f)) / d^2
         else
          -(w ⬝ᵥ (X *ᵥ w)) / d - (f ⬝ᵥ (X *ᵥ w)) / d^2)
      else
        (if j = 0 then
          -(f ⬝ᵥ (X *ᵥ f)) / d
         else
          -(f ⬝ᵥ (X *ᵥ w)) / d) := by
  fin_cases i <;> fin_cases j <;>
    simp [productFiveColumns, productFiveRows, Matrix.mul_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;> ring













end D1Bound5
end
