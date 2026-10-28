-- Prove2me | solution 1 for D1Bound5.frontier_large_bilinear_bound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:45:30.443041+00:00
-- url     : https://prove2.me/submissions/b27cc27c-0404-49b3-86ab-e5a70d0b927c

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
import Theorems.Thm_D1Bound5_QuadInt_norm_nonneg

section
open scoped NumberField Matrix.Norms.L2Operator BigOperators
open Matrix Module

namespace D1Bound5

/-- Coordinate bounds for a very unbalanced four-variable bilinear form.
The exact coefficient is 88139/270000, strictly below one third. -/
theorem _root_.solution
    (G : Matrix (Fin 4) (Fin 4) ℂ) (w : Fin 4 → ℂ) (D : ℝ)
    (hD : 0 ≤ D)
    (hG : ∀ i j, ‖G i j‖ ≤
      if i = j then (273/1000 : ℝ) else (1447/10000 : ℝ))
    (hw : ∀ i, i ≠ 3 → ‖w i‖ ≤ D/18) (hw3 : ‖w 3‖ = D) :
    ‖w ⬝ᵥ (G *ᵥ w)‖ ≤ (88139/270000 : ℝ)*D^2 := by
  let t : Fin 4 → ℝ := fun i => if i = 3 then D else D/18
  let c : Fin 4 → Fin 4 → ℝ := fun i j =>
    if i = j then (273/1000 : ℝ) else (1447/10000 : ℝ)
  have ht (i : Fin 4) : 0 ≤ t i := by dsimp [t]; split_ifs <;> positivity
  have hc (i j : Fin 4) : 0 ≤ c i j := by dsimp [c]; split_ifs <;> norm_num
  have hwt (i : Fin 4) : ‖w i‖ ≤ t i := by
    by_cases hi : i = 3
    · subst i
      simp [t, hw3]
    · simpa only [t, if_neg hi] using hw i hi
  have hid : w ⬝ᵥ (G *ᵥ w) = ∑ i : Fin 4, ∑ j : Fin 4, w i*G i j*w j := by
    simp only [dotProduct, mulVec, Finset.mul_sum, mul_assoc]
  calc
    ‖w ⬝ᵥ (G *ᵥ w)‖ = ‖∑ i : Fin 4, ∑ j : Fin 4, w i*G i j*w j‖ := congrArg norm hid
    _ ≤ ∑ i : Fin 4, ‖∑ j : Fin 4, w i*G i j*w j‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin 4, ∑ j : Fin 4, ‖w i*G i j*w j‖ := by
      apply Finset.sum_le_sum
      intro i _
      exact norm_sum_le _ _
    _ = ∑ i : Fin 4, ∑ j : Fin 4, ‖w i‖*‖G i j‖*‖w j‖ := by
      simp only [norm_mul]
    _ ≤ ∑ i : Fin 4, ∑ j : Fin 4, t i*c i j*t j := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul
        (mul_le_mul (hwt i) (hG i j) (norm_nonneg _) (ht i))
        (hwt j) (norm_nonneg _) (mul_nonneg (ht i) (hc i j))
    _ = (88139/270000 : ℝ)*D^2 := by
      simp [t, c, Fin.sum_univ_four]
      ring



end D1Bound5
end
