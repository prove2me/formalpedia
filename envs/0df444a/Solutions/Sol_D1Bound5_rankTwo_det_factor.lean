-- Prove2me | solution 1 for D1Bound5.rankTwo_det_factor
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:33:34.490751+00:00
-- url     : https://prove2.me/submissions/b865b370-71ed-4622-9abb-e8a1dc0cea72

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

/-- A four-by-four determinant under a rank-two update reduces exactly
to a two-by-two determinant; no adjoints or Hermitian hypotheses. -/
theorem _root_.solution
    (F : Matrix (Fin 4) (Fin 4) ℂ)
    (U : Matrix (Fin 4) (Fin 2) ℂ)
    (V : Matrix (Fin 2) (Fin 4) ℂ)
    (hF : F.det ≠ 0) :
    (F + U * V).det =
      F.det * ((1 : Matrix (Fin 2) (Fin 2) ℂ) + V * F⁻¹ * U).det := by
  have hu : IsUnit F.det := isUnit_iff_ne_zero.mpr hF
  have hfactor : F * (1 + (F⁻¹ * U) * V) = F + U * V := by
    calc
      F * (1 + (F⁻¹ * U) * V) =
        F + ((F * F⁻¹) * U) * V := by
          rw [Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc,
            ← Matrix.mul_assoc]
      _ = F + U * V := by
        rw [Matrix.mul_nonsing_inv F hu, Matrix.one_mul]
  rw [← hfactor, Matrix.det_mul]
  congr 1
  simpa only [Matrix.mul_assoc] using
    (Matrix.det_one_add_mul_comm (F⁻¹ * U) V)























end D1Bound5
end
