-- Prove2me | solution 1 for D1Bound5.frontier_fifteen_matrix_bounds
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:47:08.379209+00:00
-- url     : https://prove2.me/submissions/82cdc952-9aa2-4d21-a868-5225e9168430

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
import Definitions.Def_D1Bound5_FrontierFifteenRootError_Definitions
import Theorems.Thm_D1Bound5_frontier_fifteen_six_bounds

section
open scoped Matrix.Norms.L2Operator BigOperators
open Matrix

namespace D1Bound5



theorem _root_.solution (F : Matrix (Fin 4) (Fin 4) ℂ)
    (hd : ∀ i, F i i = 0) (hs : ∀ i j, F i j = F j i)
    (he : ∀ i j, i ≠ j → ‖F i j-(1/2 : ℂ)‖ ≤ frontierFifteenK i j-1/2) :
    ‖F.det‖ ≤ 1 ∧ ∀ i j, ‖F.adjugate i j‖ ≤ frontierFifteenG i j := by
  have hrepr : F =
      !![0,F 0 1,F 0 2,F 0 3; F 0 1,0,F 1 2,F 1 3;
         F 0 2,F 1 2,0,F 2 3; F 0 3,F 1 3,F 2 3,0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      (simp (config := {decide := true}) [hd] <;>
        (first | exact hs _ _ | exact (hs _ _).symm))
  have hh := frontier_fifteen_six_bounds (F 0 1) (F 0 2) (F 0 3) (F 1 2) (F 1 3) (F 2 3)
    (by simpa [frontierFifteenK] using he 0 1 (by decide))
    (by simpa [frontierFifteenK] using he 0 2 (by decide))
    (by simpa [frontierFifteenK] using he 0 3 (by decide))
    (by simpa [frontierFifteenK] using he 1 2 (by decide))
    (by simpa [frontierFifteenK] using he 1 3 (by decide))
    (by simpa [frontierFifteenK] using he 2 3 (by decide))
  simpa only [← hrepr] using hh



end D1Bound5
end
