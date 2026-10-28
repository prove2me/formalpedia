-- Prove2me | solution 1 for D1Bound5.finiteN3_coefficient_sums
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:29:31.412995+00:00
-- url     : https://prove2.me/submissions/8a71dc88-500f-472c-b6cd-166fdcab376d

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
import Definitions.Def_D1Bound5_FiniteN3Height_Definitions

section
namespace D1Bound5














/-- Integer coefficient sums computed from the actual vectors. Taking
the maximum separately in each degree still leaves strict slack at4143. -/
theorem _root_.solution (i : Fin 3) :
    ((∑ j, |(finiteN3Coeff0 i 0 j : ℝ)|)+
      (∑ j, |(finiteN3Coeff0 i 1 j : ℝ)|) ≤ 342) ∧
    ((∑ j, |(finiteN3Coeff1 i 0 j : ℝ)|)+
      (∑ j, |(finiteN3Coeff1 i 1 j : ℝ)|) ≤ 2352) ∧
    ((∑ j, |(finiteN3Coeff2 i 0 j : ℝ)|)+
      (∑ j, |(finiteN3Coeff2 i 1 j : ℝ)|) ≤ 5792) ∧
    ((∑ j, |(finiteN3Coeff3 i 0 j : ℝ)|)+
      (∑ j, |(finiteN3Coeff3 i 1 j : ℝ)|) ≤ 4096) := by
  fin_cases i <;> norm_num [finiteN3Coeff0,finiteN3Coeff1,finiteN3Coeff2,
    finiteN3Coeff3,Fin.sum_univ_succ]







end D1Bound5
end
