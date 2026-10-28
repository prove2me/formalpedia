-- Prove2me | solution 1 for D1Bound5.frontier_large_rankOne_det_bound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:29:24.320991+00:00
-- url     : https://prove2.me/submissions/6f2dac00-6e25-467f-b5c4-1059a0f79cb0

import Lean.Util.CollectAxioms
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Theorems.Thm_D1Bound5_adjugate_eq_det_smul_inverse
import Theorems.Thm_D1Bound5_frontier_large_bilinear_bound
import Theorems.Thm_D1Bound5_rankOneDeterminant

section
open scoped NumberField Matrix.Norms.L2Operator BigOperators
open Matrix Module

namespace D1Bound5



/-- The entrywise adjugate estimate sharpens the previous product-four
constant two to three after the already-proved first growth step. -/
theorem _root_.solution
    (F : Matrix (Fin 4) (Fin 4) ℂ) (w : Fin 4 → ℂ) (D : ℝ)
    (hD : 54 ≤ D) (hF : F.det ≠ 0) (hdet : ‖F.det‖ < (1/4 : ℝ))
    (hG : ∀ i j, ‖F.adjugate i j‖ ≤
      if i = j then (273/1000 : ℝ) else (1447/10000 : ℝ))
    (hw : ∀ i, i ≠ 3 → ‖w i‖ ≤ D/18) (hw3 : ‖w 3‖ = D) :
    ‖(F+Matrix.vecMulVec w w).det‖ < D^2/3 := by
  have hD0 : 0 ≤ D := by linarith only [hD]
  have hbil := frontier_large_bilinear_bound F.adjugate w D hD0 hG hw hw3
  have hadj : w ⬝ᵥ (F.adjugate *ᵥ w) = F.det*(w ⬝ᵥ (F⁻¹ *ᵥ w)) := by
    simp only [adjugate_eq_det_smul_inverse F hF, Matrix.smul_mulVec,
      dotProduct_smul, smul_eq_mul]
  have hid : (F+Matrix.vecMulVec w w).det = F.det+w ⬝ᵥ (F.adjugate *ᵥ w) := by
    rw [rankOneDeterminant F w hF, hadj]
    ring
  have hsq : 2916 ≤ D^2 := by nlinarith only [hD, sq_nonneg (D-54)]
  have hnum : (1/4 : ℝ)+(88139/270000 : ℝ)*D^2 < D^2/3 := by
    nlinarith only [hsq]
  rw [hid]
  exact (norm_add_le _ _).trans_lt (by linarith only [hdet, hbil, hnum])

end D1Bound5
end
