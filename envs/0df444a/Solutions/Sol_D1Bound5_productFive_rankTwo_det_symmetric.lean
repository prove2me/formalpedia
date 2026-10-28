-- Prove2me | solution 1 for D1Bound5.productFive_rankTwo_det_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:37:40.506327+00:00
-- url     : https://prove2.me/submissions/a786cfbc-26f6-4ff8-b546-5f9bbdf6ebdc

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
import Theorems.Thm_D1Bound5_productFive_rankTwo_det_general
import Theorems.Thm_D1Bound5_symmetric_inverse_bilinear_swap

section
open Matrix

namespace D1Bound5

















/-- Exactly the manuscript's rank-two determinant polynomial, before
identifying the four-by-four update with the Schur complement. -/
theorem _root_.solution
    (F : Matrix (Fin 4) (Fin 4) ℂ)
    (f w : Fin 4 → ℂ) (d : ℂ)
    (hF : F.det ≠ 0) (hd : d ≠ 0)
    (hsym : Fᵀ = F) :
    (F + productFiveColumns f w * productFiveRows f w d).det =
      F.det *
        (1 - 2 * (f ⬝ᵥ (F⁻¹ *ᵥ w)) / d +
          ((f ⬝ᵥ (F⁻¹ *ᵥ w))^2 -
            (f ⬝ᵥ (F⁻¹ *ᵥ f)) * (w ⬝ᵥ (F⁻¹ *ᵥ w)) -
            (f ⬝ᵥ (F⁻¹ *ᵥ f))) / d^2) := by
  rw [productFive_rankTwo_det_general F f w d hF hd,
    symmetric_inverse_bilinear_swap F f w hsym]
  ring







end D1Bound5
end
