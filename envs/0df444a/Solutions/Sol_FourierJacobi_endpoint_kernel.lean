-- Prove2me | solution 1 for FourierJacobi.endpoint_kernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:41:30.942483+00:00
-- url     : https://prove2.me/submissions/19a5b1d8-8265-462d-acb2-fb0d34b29173

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
theorem _root_.solution (q : K) (hq : q ≠ 1) (v : Fin 2 → K) :
    (intertwinerMatrix q q⁻¹).mulVec v = 0 ↔ v 1 = -q⁻¹ * v 0 := by
  rw [intertwinerMatrix_at_endpoint q hq]
  simp [dotProduct, Fin.sum_univ_two, funext_iff, Fin.forall_fin_two]
  constructor <;> intro h <;> linear_combination h
end FourierJacobi
