-- Prove2me | solution 1 for D1Bound5.productFiveIntegratedBlock_det
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:51:45.339219+00:00
-- url     : https://prove2.me/submissions/8052dcbf-fcc9-4e4c-a811-dd178cb5683c

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
import Definitions.Def_D1Bound5_ProductFiveBlockDet_Definitions
import Definitions.Def_D1Bound5_ProductFiveRankTwo_Definitions
import Theorems.Thm_D1Bound5_scalar_last_block_det

section
open Matrix

namespace D1Bound5





/-- Exact block determinant in equation (integrated-3), without requiring
the leading four-by-four matrix to be nonsingular. -/
theorem _root_.solution
    (F : Matrix (Fin 4) (Fin 4) ℂ)
    (f w : Fin 4 → ℂ) (d : ℂ) (hd : d ≠ 0) :
    (productFiveIntegratedBlock F f w d).det =
      d^2 * (productFiveSchur F f w d).det := by
  have hmat :
      F + Matrix.of (fun i j => w i * w j) -
          Matrix.of (fun i j => (f i + d * w i) * (f j + d * w j) / d^2) =
        productFiveSchur F f w d := by
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.of_apply,
      productFiveSchur]
    field_simp [hd]
    ring
  unfold productFiveIntegratedBlock
  rw [scalar_last_block_det _ (fun i => f i + d * w i)
    (fun j => f j + d * w j) (d^2) (pow_ne_zero 2 hd)]
  rw [hmat]

end D1Bound5
end
