-- Prove2me | solution 1 for D1Bound5.rankTwo_det_entries
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:22:20.183405+00:00
-- url     : https://prove2.me/submissions/ddebe612-795b-4a1a-9a75-e8f017f442be

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
import Theorems.Thm_D1Bound5_rankTwo_det_factor

section
open Matrix

namespace D1Bound5



/-- The explicit two-by-two determinant, with both off-diagonal products
retained. This is valid even for nonsymmetric complex F. -/
theorem _root_.solution
    (F : Matrix (Fin 4) (Fin 4) ℂ)
    (U : Matrix (Fin 4) (Fin 2) ℂ)
    (V : Matrix (Fin 2) (Fin 4) ℂ)
    (hF : F.det ≠ 0) :
    (F + U * V).det = F.det *
      ((1 + (V * F⁻¹ * U) 0 0) *
        (1 + (V * F⁻¹ * U) 1 1) -
        (V * F⁻¹ * U) 0 1 * (V * F⁻¹ * U) 1 0) := by
  rw [rankTwo_det_factor F U V hF]
  simp only [Matrix.det_fin_two, Matrix.add_apply]
  norm_num [Matrix.one_apply]





















end D1Bound5
end
