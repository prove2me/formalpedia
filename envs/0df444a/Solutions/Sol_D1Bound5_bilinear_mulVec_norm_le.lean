-- Prove2me | solution 1 for D1Bound5.bilinear_mulVec_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:29:09.916502+00:00
-- url     : https://prove2.me/submissions/ba075776-b0dd-4fe6-a91a-cb2c399369ad

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

/-- The modulus of a complex bilinear quadratic form is bounded by the
Euclidean operator norm. No Hermitian or symmetry assumption is needed. -/
theorem _root_.solution (F : Matrix (Fin 4) (Fin 4) ℂ)
    (w : Fin 4 → ℂ) :
    ‖w ⬝ᵥ (F *ᵥ w)‖ ≤ ‖F‖ * (∑ i, ‖w i‖ ^ 2) := by
  let x : EuclideanSpace ℂ (Fin 4) := WithLp.toLp 2 w
  let y : EuclideanSpace ℂ (Fin 4) := WithLp.toLp 2 (star w)
  have hy : ‖y‖ = ‖x‖ := by
    have hsq : ‖y‖ ^ 2 = ‖x‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq y, EuclideanSpace.norm_sq_eq x]
      simp [x, y]
    nlinarith only [hsq, norm_nonneg x, norm_nonneg y]
  have hinner : w ⬝ᵥ (F *ᵥ w) =
      inner ℂ y ((EuclideanSpace.equiv (Fin 4) ℂ).symm (F *ᵥ w)) := by
    change w ⬝ᵥ (F *ᵥ w) = inner ℂ (WithLp.toLp 2 (star w))
      (WithLp.toLp 2 (F *ᵥ w))
    rw [EuclideanSpace.inner_toLp_toLp]
    simp [dotProduct_comm]
  have hv : ‖(EuclideanSpace.equiv (Fin 4) ℂ).symm (F *ᵥ w)‖ ≤ ‖F‖ * ‖x‖ := by
    simpa only [x] using Matrix.l2_opNorm_mulVec F x
  calc
    ‖w ⬝ᵥ (F *ᵥ w)‖ =
        ‖inner ℂ y ((EuclideanSpace.equiv (Fin 4) ℂ).symm (F *ᵥ w))‖ :=
          congrArg norm hinner
    _ ≤ ‖y‖ * ‖(EuclideanSpace.equiv (Fin 4) ℂ).symm (F *ᵥ w)‖ :=
      norm_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖F‖ * ‖x‖) := by
      rw [hy]
      exact mul_le_mul_of_nonneg_left hv (norm_nonneg x)
    _ = ‖F‖ * (∑ i, ‖w i‖ ^ 2) := by
      rw [← EuclideanSpace.norm_sq_eq x]
      ring









end D1Bound5
end
