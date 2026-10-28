-- Prove2me | solution 1 for D1Bound5.IsD1Tuple.frontier_small_norm_growth
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:20:20.939995+00:00
-- url     : https://prove2.me/submissions/fd3a7721-f427-4a3b-a325-4d1c6f7b0cd4

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
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FrontierTableNumeric_Definitions
import Definitions.Def_D1Bound5_IsD1Tuple
import Theorems.Thm_D1Bound5_IsD1Tuple_frontier_table_growth
import Theorems.Thm_D1Bound5_QuadInt_norm_nonneg

section
open scoped NumberField
open Module

namespace D1Bound5

/-- The five manuscript rows expressed using actual squared complex
modulus, which the full-ring bridge identifies with the integral norm. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a : Fin 4 → 𝓞 K) (ha : IsD1Tuple a)
    (hmon : Monotone (fun i => ‖phi (a i : K)‖))
    (hN8 : ‖phi (a 0 : K)‖^2 ≤ 8) :
    let A := ‖phi (a 0 : K)‖
    let B := ‖phi (a 1 : K)‖
    let C := ‖phi (a 2 : K)‖
    let D := ‖phi (a 3 : K)‖
    (A^2 = 1 → 8 ≤ B → (27/8 : ℝ)*A*B*C < D) ∧
    (A^2 = 2 → 4 ≤ B → 3*A*B*C < D) ∧
    (A^2 = 3 → 3 ≤ B → (11/4 : ℝ)*A*B*C < D) ∧
    (A^2 = 4 → 3 ≤ B → (29/10 : ℝ)*A*B*C < D) ∧
    (5 ≤ A^2 → 3 ≤ B → 3*A*B*C < D) := by
  let A := ‖phi (a 0 : K)‖
  let B := ‖phi (a 1 : K)‖
  let C := ‖phi (a 2 : K)‖
  let D := ‖phi (a 3 : K)‖
  change (A^2 = 1 → 8 ≤ B → (27/8 : ℝ)*A*B*C < D) ∧
    (A^2 = 2 → 4 ≤ B → 3*A*B*C < D) ∧
    (A^2 = 3 → 3 ≤ B → (11/4 : ℝ)*A*B*C < D) ∧
    (A^2 = 4 → 3 ≤ B → (29/10 : ℝ)*A*B*C < D) ∧
    (5 ≤ A^2 → 3 ≤ B → 3*A*B*C < D)
  have hA0 : 0 ≤ A := norm_nonneg _
  have hsmall : A < 3 := by
    by_contra h
    have hp := mul_nonneg (sub_nonneg.mpr (le_of_not_gt h))
      (show 0 ≤ A+3 by linarith only [hA0])
    nlinarith only [hN8, hp]
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro hN hB
    have hA : (1 : ℝ) ≤ A := (sq_le_sq₀ (by norm_num) hA0).mp (by rw [hN]; norm_num)
    exact IsD1Tuple.frontier_table_growth hK phi a ha hmon 1 8 (27/8)
      (by norm_num [FrontierTableRow]) hA hB hsmall
  · intro hN hB
    have hA : (140/99 : ℝ) ≤ A :=
      (sq_le_sq₀ (by norm_num) hA0).mp (by rw [hN]; norm_num)
    exact IsD1Tuple.frontier_table_growth hK phi a ha hmon (140/99) 4 3
      (by norm_num [FrontierTableRow]) hA hB hsmall
  · intro hN hB
    have hA : (12/7 : ℝ) ≤ A :=
      (sq_le_sq₀ (by norm_num) hA0).mp (by rw [hN]; norm_num)
    exact IsD1Tuple.frontier_table_growth hK phi a ha hmon (12/7) 3 (11/4)
      (by norm_num [FrontierTableRow]) hA hB hsmall
  · intro hN hB
    have hA : (2 : ℝ) ≤ A := (sq_le_sq₀ (by norm_num) hA0).mp (by rw [hN]; norm_num)
    exact IsD1Tuple.frontier_table_growth hK phi a ha hmon 2 3 (29/10)
      (by norm_num [FrontierTableRow]) hA hB hsmall
  · intro hN hB
    have hA : (20/9 : ℝ) ≤ A :=
      (sq_le_sq₀ (by norm_num) hA0).mp (by nlinarith only [hN])
    exact IsD1Tuple.frontier_table_growth hK phi a ha hmon (20/9) 3 3
      (by norm_num [FrontierTableRow]) hA hB hsmall

end D1Bound5
end
