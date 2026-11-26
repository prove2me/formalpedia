-- Prove2me | solution 1 for FourierJacobi.endpoint_kills_specialVector
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:41:30.220723+00:00
-- url     : https://prove2.me/submissions/9501739e-7d1d-4012-b853-f45165f0b739

import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Definitions.Def_FourierJacobi_Algebra_Intertwiner
import Theorems.Thm_FourierJacobi_intertwinerMatrix_at_endpoint

set_option autoImplicit false
open FourierJacobi
open Matrix
variable {K : Type*} [Field K]
namespace FourierJacobi
theorem _root_.solution (q : K) (hq : q ≠ 1) :
    (intertwinerMatrix q q⁻¹).mulVec (specialVector q) = 0 := by
  rw [intertwinerMatrix_at_endpoint q hq]
  ext i
  fin_cases i <;> simp [specialVector, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
end FourierJacobi
