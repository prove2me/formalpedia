-- Prove2me | solution 1 for FourierJacobi.intertwinerMatrix_at_endpoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:40:47.808131+00:00
-- url     : https://prove2.me/submissions/3d4ed1c7-9f2c-4d2e-9069-402ed3609f03

import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Definitions.Def_FourierJacobi_Algebra_Intertwiner

set_option autoImplicit false
open FourierJacobi
open Matrix
variable {K : Type*} [Field K]
namespace FourierJacobi
theorem _root_.solution (q : K) (hq : q ≠ 1) :
    intertwinerMatrix q q⁻¹ = !![q⁻¹, 1; q⁻¹, 1] := by
  have hr : 1 - q⁻¹ ≠ 0 := sub_ne_zero.mpr (Ne.symm (inv_ne_one.mpr hq))
  ext i j
  fin_cases i <;> fin_cases j <;> simp [intertwinerMatrix, hr]
end FourierJacobi
