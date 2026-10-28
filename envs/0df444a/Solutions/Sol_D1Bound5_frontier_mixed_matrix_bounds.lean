-- Prove2me | solution 1 for D1Bound5.frontier_mixed_matrix_bounds
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:28:59.406545+00:00
-- url     : https://prove2.me/submissions/b41d7973-8ad8-4b76-a057-b74d048002cf

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
import Theorems.Thm_D1Bound5_frontier_mixed_six_bounds

section
open scoped NumberField Matrix.Norms.L2Operator BigOperators
open Matrix Module

namespace D1Bound5

/-- The mixed six-variable cofactor bounds apply to any symmetric
zero-diagonal matrix with the designated first-row error envelope. -/
theorem _root_.solution (F : Matrix (Fin 4) (Fin 4) ℂ) (k l : ℝ)
    (hl : (1/2 : ℝ) ≤ l) (hlk : l ≤ k)
    (hd : ∀ i, F i i = 0) (hs : ∀ i j, F i j = F j i)
    (hfirst : ∀ i j, i ≠ j → i = 0 ∨ j = 0 →
      ‖F i j-(1/2 : ℂ)‖ ≤ k-1/2)
    (hlater : ∀ i j, i ≠ j → ¬(i = 0 ∨ j = 0) →
      ‖F i j-(1/2 : ℂ)‖ ≤ l-1/2) :
    ‖F.det‖ ≤ 9*k^2*l^2 ∧
    ∀ i j, ‖F.adjugate i j‖ ≤ if i = j then 2*(k^2*l) else 3*(k^2*l)-1/4 := by
  have hrepr : F =
      !![0,F 0 1,F 0 2,F 0 3;
         F 0 1,0,F 1 2,F 1 3;
         F 0 2,F 1 2,0,F 2 3;
         F 0 3,F 1 3,F 2 3,0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      (simp (config := {decide := true}) [hd] <;>
        (first | exact hs _ _ | exact (hs _ _).symm))
  have h := frontier_mixed_six_bounds
    (F 0 1) (F 0 2) (F 0 3) (F 1 2) (F 1 3) (F 2 3) k l hl hlk
    (hfirst 0 1 (by decide) (by decide))
    (hfirst 0 2 (by decide) (by decide))
    (hfirst 0 3 (by decide) (by decide))
    (hlater 1 2 (by decide) (by decide))
    (hlater 1 3 (by decide) (by decide))
    (hlater 2 3 (by decide) (by decide))
  exact (congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ =>
    ‖M.det‖ ≤ 9*k^2*l^2 ∧
      ∀ i j, ‖M.adjugate i j‖ ≤
        if i = j then 2*(k^2*l) else 3*(k^2*l)-1/4) hrepr).mpr h



end D1Bound5
end
