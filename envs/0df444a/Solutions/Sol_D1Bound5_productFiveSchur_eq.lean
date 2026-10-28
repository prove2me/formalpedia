-- Prove2me | solution 1 for D1Bound5.productFiveSchur_eq
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:16:23.371359+00:00
-- url     : https://prove2.me/submissions/655a0cc1-28fd-4b6f-94d1-4fc53372ac0f

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









/-- Exact matrix equality before applying the rank-two determinant lemma.
No nonzero or invertibility assumptions are required for this identity. -/
theorem productFive_update_entry (f w : Fin 4 → ℂ) (d : ℂ)
    (i j : Fin 4) :
    (productFiveColumns f w * productFiveRows f w d) i j =
      -((w i * f j + f i * w j) / d) - f i * f j / d^2 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two,
    productFiveColumns, productFiveRows]
  ring











/-- The Schur complement is exactly the rank-two perturbation. -/
theorem _root_.solution
    (F : Matrix (Fin 4) (Fin 4) ℂ)
    (f w : Fin 4 → ℂ) (d : ℂ) :
    productFiveSchur F f w d =
      F + productFiveColumns f w * productFiveRows f w d := by
  ext i j
  change F i j - (w i * f j + f i * w j) / d -
    f i * f j / d^2 =
      F i j + (productFiveColumns f w *
        productFiveRows f w d) i j
  rw [productFive_update_entry]
  ring



end D1Bound5
end
