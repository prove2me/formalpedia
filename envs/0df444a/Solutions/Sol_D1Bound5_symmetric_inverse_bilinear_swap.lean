-- Prove2me | solution 1 for D1Bound5.symmetric_inverse_bilinear_swap
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:30:18.74665+00:00
-- url     : https://prove2.me/submissions/73dc5b0c-5a57-48af-8997-c98224878e8b

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

section
open Matrix

namespace D1Bound5















/-- Symmetry of the complex bilinear form of the inverse. No complex
conjugation occurs; this is the ordinary transpose. -/
theorem _root_.solution
    (F : Matrix (Fin 4) (Fin 4) ℂ) (f w : Fin 4 → ℂ)
    (hsym : Fᵀ = F) :
    w ⬝ᵥ (F⁻¹ *ᵥ f) = f ⬝ᵥ (F⁻¹ *ᵥ w) := by
  have hinv : (F⁻¹)ᵀ = F⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hsym]
  simpa only [hinv] using
    (Matrix.dotProduct_transpose_mulVec (F⁻¹) w f)









end D1Bound5
end
