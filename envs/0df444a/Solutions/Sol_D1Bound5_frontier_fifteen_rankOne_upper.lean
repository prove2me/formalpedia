-- Prove2me | solution 1 for D1Bound5.frontier_fifteen_rankOne_upper
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:21:54.687184+00:00
-- url     : https://prove2.me/submissions/d4b07048-a5fe-416e-9507-66fc3645b0f8

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
import Definitions.Def_D1Bound5_FrontierFifteenCofactors_Definitions
import Theorems.Thm_D1Bound5_QuadInt_norm_nonneg
import Theorems.Thm_D1Bound5_adjugate_eq_det_smul_inverse
import Theorems.Thm_D1Bound5_rankOneDeterminant

section
open scoped Matrix.Norms.L2Operator BigOperators
open Matrix

namespace D1Bound5





theorem _root_.solution
    (F : Matrix (Fin 4) (Fin 4) ℂ) (w : Fin 4 → ℂ)
    (hF : F.det ≠ 0) (hdet : ‖F.det‖ ≤ 1)
    (hG : ∀ i j, ‖F.adjugate i j‖ ≤ frontierFifteenG i j) :
    ‖(F+Matrix.vecMulVec w w).det‖ ≤
      (252/1000 : ℝ)*‖w 0‖^2+(256/1000)*‖w 1‖^2+(277/1000)*‖w 2‖^2+(282/1000)*‖w 3‖^2+
      (284/1000)*‖w 0‖*‖w 1‖+(284/1000)*‖w 0‖*‖w 2‖+(288/1000)*‖w 0‖*‖w 3‖+
      (286/1000)*‖w 1‖*‖w 2‖+(296/1000)*‖w 1‖*‖w 3‖+(362/1000)*‖w 2‖*‖w 3‖+1 := by
  have hadj : w ⬝ᵥ (F.adjugate *ᵥ w) = F.det*(w ⬝ᵥ (F⁻¹ *ᵥ w)) := by
    simp only [adjugate_eq_det_smul_inverse F hF,Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul]
  have hid : (F+Matrix.vecMulVec w w).det = F.det+w ⬝ᵥ (F.adjugate *ᵥ w) := by
    rw [rankOneDeterminant F w hF,hadj]
    ring
  have hform : w ⬝ᵥ (F.adjugate *ᵥ w) =
      ∑ i : Fin 4, ∑ j : Fin 4, w i*F.adjugate i j*w j := by
    simp only [dotProduct,mulVec,Finset.mul_sum,mul_assoc]
  have hbil : ‖w ⬝ᵥ (F.adjugate *ᵥ w)‖ ≤
      ∑ i : Fin 4, ∑ j : Fin 4, ‖w i‖*frontierFifteenG i j*‖w j‖ := by
    rw [hform]
    calc
      _ ≤ ∑ i : Fin 4, ‖∑ j : Fin 4, w i*F.adjugate i j*w j‖ := norm_sum_le _ _
      _ ≤ ∑ i : Fin 4, ∑ j : Fin 4, ‖w i*F.adjugate i j*w j‖ := by
        apply Finset.sum_le_sum
        intro i _
        exact norm_sum_le _ _
      _ = ∑ i : Fin 4, ∑ j : Fin 4, ‖w i‖*‖F.adjugate i j‖*‖w j‖ := by simp only [norm_mul]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hG i j) (norm_nonneg _)) (norm_nonneg _)
  rw [hid]
  have hh := norm_add_le F.det (w ⬝ᵥ (F.adjugate *ᵥ w))
  simp [frontierFifteenG,Fin.sum_univ_four] at hbil
  nlinarith only [hh,hdet,hbil]

end D1Bound5
end
