-- Prove2me | solution 1 for D1Bound5.productFiveSchur_det
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:21:45.161313+00:00
-- url     : https://prove2.me/submissions/90672eab-0e3d-4a33-9f9a-d7644c0b52a7

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
import Theorems.Thm_D1Bound5_productFiveSchur_eq
import Theorems.Thm_D1Bound5_productFive_rankTwo_det_symmetric

section
open Matrix

namespace D1Bound5























/-- Exact equation (integrated-3)'s determinant identity in the manuscript:
the complex bilinear transpose is NOT a conjugate transpose. -/
theorem _root_.solution
    (F : Matrix (Fin 4) (Fin 4) ℂ)
    (f w : Fin 4 → ℂ) (d : ℂ)
    (hF : F.det ≠ 0) (hd : d ≠ 0)
    (hsym : Fᵀ = F) :
    (productFiveSchur F f w d).det =
      F.det *
        (1 - 2 * (f ⬝ᵥ (F⁻¹ *ᵥ w)) / d +
          ((f ⬝ᵥ (F⁻¹ *ᵥ w))^2 -
            (f ⬝ᵥ (F⁻¹ *ᵥ f)) * (w ⬝ᵥ (F⁻¹ *ᵥ w)) -
            (f ⬝ᵥ (F⁻¹ *ᵥ f))) / d^2) := by
  rw [productFiveSchur_eq]
  exact productFive_rankTwo_det_symmetric F f w d hF hd hsym

end D1Bound5
end
