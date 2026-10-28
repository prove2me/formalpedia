-- Prove2me | solution 1 for D1Bound5.finiteMTerms_weight
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:44:13.562658+00:00
-- url     : https://prove2.me/submissions/7fb23cba-8a7a-420a-8c7a-93fc5827d789

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FiniteMMatrix_Definitions

section
namespace D1Bound5





















/-- The complete finite row certificate; it requires no norm or analytic
assumption. In row zero the exact sum is38400, in the other rows169728. -/
theorem _root_.solution (i : Fin 4) :
    (∑ j : Fin 3, ((finiteMTerms i j.succ).map finiteMTermWeight).sum) ≤ 169728 := by
  fin_cases i <;> decide






end D1Bound5
end
