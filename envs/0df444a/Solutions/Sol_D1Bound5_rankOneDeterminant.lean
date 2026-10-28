-- Prove2me | solution 1 for D1Bound5.rankOneDeterminant
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:25:02.654631+00:00
-- url     : https://prove2.me/submissions/97e09989-1345-4e24-9bb6-ad92af342c41

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
open scoped Matrix.Norms.L2Operator
open scoped InnerProductSpace
open Matrix

namespace D1Bound5



/-- The determinant lemma for a symmetric algebraic rank-one update in
dimension four. This holds for complex vectors without conjugation. -/
theorem _root_.solution (F : Matrix (Fin 4) (Fin 4) ℂ)
    (w : Fin 4 → ℂ) (hF : F.det ≠ 0) :
    (F + Matrix.vecMulVec w w).det =
      F.det * (1 + w ⬝ᵥ (F⁻¹ *ᵥ w)) := by
  have hu : IsUnit F.det := isUnit_iff_ne_zero.mpr hF
  have hfactor : F + Matrix.vecMulVec w w =
      F * (1 + F⁻¹ * Matrix.vecMulVec w w) := by
    rw [Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv F hu, Matrix.one_mul]
  have hrank : F⁻¹ * Matrix.vecMulVec w w =
      Matrix.replicateCol (Fin 1) (F⁻¹ *ᵥ w) * Matrix.replicateRow (Fin 1) w := by
    rw [Matrix.vecMulVec_eq (Fin 1), ← Matrix.mul_assoc,
      ← Matrix.replicateCol_mulVec]
    rfl
  have hdet : (1 + Matrix.replicateCol (Fin 1) (F⁻¹ *ᵥ w) *
      Matrix.replicateRow (Fin 1) w).det = 1 + w ⬝ᵥ (F⁻¹ *ᵥ w) :=
    Matrix.det_one_add_replicateCol_mul_replicateRow (F⁻¹ *ᵥ w) w
  rw [hfactor, Matrix.det_mul, hrank, hdet]







end D1Bound5
end
