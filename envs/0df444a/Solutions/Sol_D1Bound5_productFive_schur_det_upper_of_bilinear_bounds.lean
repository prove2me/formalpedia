-- Prove2me | solution 1 for D1Bound5.productFive_schur_det_upper_of_bilinear_bounds
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:39:00.91595+00:00
-- url     : https://prove2.me/submissions/b5b5c5dc-fa00-4e31-80c0-298c829e3cf9

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
import Theorems.Thm_D1Bound5_productFiveSchur_det
import Theorems.Thm_D1Bound5_productFive_scalar_det_upper

section
open Matrix

namespace D1Bound5



/-- Apply the scalar margin to the actual rank-two Schur complement.
The remaining hypotheses are precisely the normalized analytic estimates. -/
theorem _root_.solution
    (F : Matrix (Fin 4) (Fin 4) ℂ)
    (f w : Fin 4 → ℂ) (d : ℂ)
    (hF : F.det ≠ 0) (hd : d ≠ 0)
    (hsym : Fᵀ = F)
    (ha : ‖F.det‖ ≤ (33/128 : ℝ))
    (hh : ‖(f ⬝ᵥ (F⁻¹ *ᵥ w))/d‖ ≤ (11/108 : ℝ))
    (hp : ‖f ⬝ᵥ (F⁻¹ *ᵥ f)‖ ≤ (1 : ℝ))
    (hq : ‖(w ⬝ᵥ (F⁻¹ *ᵥ w))/d^2‖ ≤ (8/243 : ℝ))
    (hpd : ‖(f ⬝ᵥ (F⁻¹ *ᵥ f))/d^2‖ ≤ (1/2916 : ℝ)) :
    ‖(productFiveSchur F f w d).det‖ < (1/3 : ℝ) := by
  rw [productFiveSchur_det F f w d hF hd hsym]
  exact productFive_scalar_det_upper F.det
    (f ⬝ᵥ (F⁻¹ *ᵥ w)) (f ⬝ᵥ (F⁻¹ *ᵥ f))
    (w ⬝ᵥ (F⁻¹ *ᵥ w)) d hd ha hh hp hq hpd

end D1Bound5
end
