-- Prove2me | solution 1 for D1Bound5.frontier_mixed_rankOne_upper
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:29:03.317001+00:00
-- url     : https://prove2.me/submissions/e5511013-5c03-46af-a4f2-6e8503f9306d

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
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Theorems.Thm_D1Bound5_QuadInt_norm_nonneg
import Theorems.Thm_D1Bound5_adjugate_eq_det_smul_inverse
import Theorems.Thm_D1Bound5_rankOneDeterminant

section
open scoped NumberField Matrix.Norms.L2Operator BigOperators
open Matrix Module

namespace D1Bound5



/-- The exact integrated-four-entry bound before division by ABST. This
retains the leading cubic cancellation in off-diagonal cofactors. -/
theorem _root_.solution
    (F : Matrix (Fin 4) (Fin 4) ℂ) (w : Fin 4 → ℂ) (K Q : ℝ)
    (hF : F.det ≠ 0) (hdet : ‖F.det‖ ≤ Q)
    (hG : ∀ i j, ‖F.adjugate i j‖ ≤ if i = j then 2*K else 3*K-1/4) :
    ‖(F+Matrix.vecMulVec w w).det‖ ≤
      2*K*(‖w 0‖^2+‖w 1‖^2+‖w 2‖^2+‖w 3‖^2)+
      (6*K-1/2)*(‖w 0‖*‖w 1‖+‖w 0‖*‖w 2‖+‖w 0‖*‖w 3‖+
        ‖w 1‖*‖w 2‖+‖w 1‖*‖w 3‖+‖w 2‖*‖w 3‖)+Q := by
  have hadj : w ⬝ᵥ (F.adjugate *ᵥ w) = F.det*(w ⬝ᵥ (F⁻¹ *ᵥ w)) := by
    simp only [adjugate_eq_det_smul_inverse F hF, Matrix.smul_mulVec,
      dotProduct_smul, smul_eq_mul]
  have hid : (F+Matrix.vecMulVec w w).det = F.det+w ⬝ᵥ (F.adjugate *ᵥ w) := by
    rw [rankOneDeterminant F w hF, hadj]
    ring
  have hform : w ⬝ᵥ (F.adjugate *ᵥ w) =
      ∑ i : Fin 4, ∑ j : Fin 4, w i*F.adjugate i j*w j := by
    simp only [dotProduct, mulVec, Finset.mul_sum, mul_assoc]
  have hbil : ‖w ⬝ᵥ (F.adjugate *ᵥ w)‖ ≤
      ∑ i : Fin 4, ∑ j : Fin 4,
        ‖w i‖*(if i = j then 2*K else 3*K-1/4)*‖w j‖ := by
    rw [hform]
    calc
      _ ≤ ∑ i : Fin 4, ‖∑ j : Fin 4, w i*F.adjugate i j*w j‖ := norm_sum_le _ _
      _ ≤ ∑ i : Fin 4, ∑ j : Fin 4, ‖w i*F.adjugate i j*w j‖ := by
        apply Finset.sum_le_sum
        intro i _
        exact norm_sum_le _ _
      _ = ∑ i : Fin 4, ∑ j : Fin 4, ‖w i‖*‖F.adjugate i j‖*‖w j‖ := by
        simp only [norm_mul]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hG i j) (norm_nonneg _)) (norm_nonneg _)
  have hsum : (∑ i : Fin 4, ∑ j : Fin 4,
        ‖w i‖*(if i = j then 2*K else 3*K-1/4)*‖w j‖) =
      2*K*(‖w 0‖^2+‖w 1‖^2+‖w 2‖^2+‖w 3‖^2)+
      (6*K-1/2)*(‖w 0‖*‖w 1‖+‖w 0‖*‖w 2‖+‖w 0‖*‖w 3‖+
        ‖w 1‖*‖w 2‖+‖w 1‖*‖w 3‖+‖w 2‖*‖w 3‖) := by
    simp [Fin.sum_univ_four]
    ring
  rw [hsum] at hbil
  rw [hid]
  have h := norm_add_le F.det (w ⬝ᵥ (F.adjugate *ᵥ w))
  linarith only [h, hdet, hbil]

end D1Bound5
end
