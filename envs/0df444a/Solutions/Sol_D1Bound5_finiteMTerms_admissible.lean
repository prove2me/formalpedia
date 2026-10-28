-- Prove2me | solution 1 for D1Bound5.finiteMTerms_admissible
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:51:53.65741+00:00
-- url     : https://prove2.me/submissions/adb808ba-99fa-40a2-87cf-d4d14569750a

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FiniteMMatrix_Definitions

section
namespace D1Bound5



















/-- Every root-column monomial has the required anchor and terminal weights. -/
theorem _root_.solution (i : Fin 4) (j : Fin 3) :
    ∀ t ∈ finiteMTerms i j.succ, finiteMTermAdmissible t := by
  fin_cases i <;> fin_cases j <;> decide








end D1Bound5
end
