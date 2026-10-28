-- Prove2me | solution 1 for D1Bound5.finiteN2_coefficient_sums
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:21:39.959286+00:00
-- url     : https://prove2.me/submissions/41748fc2-3021-435e-bb9c-99fcb36217a6

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FiniteN2Height_Definitions

section
namespace D1Bound5









/-- The coefficient sums are computed from the actual integer vectors,
not supplied as table data in a hypothesis. -/
theorem _root_.solution (i : Fin 3) :
    ((∑ j, |(finiteN2Coeff0 i 0 j : ℝ)|) +
      (∑ j, |(finiteN2Coeff0 i 1 j : ℝ)|) ≤ 50) ∧
    ((∑ j, |(finiteN2Coeff1 i 0 j : ℝ)|) +
      (∑ j, |(finiteN2Coeff1 i 1 j : ℝ)|) ≤ 200) ∧
    ((∑ j, |(finiteN2Coeff2 i 0 j : ℝ)|) +
      (∑ j, |(finiteN2Coeff2 i 1 j : ℝ)|) ≤ 240) := by
  fin_cases i <;> norm_num [finiteN2Coeff0, finiteN2Coeff1, finiteN2Coeff2,
    Fin.sum_univ_succ]







end D1Bound5
end
