-- Prove2me | solution 1 for FourierJacobi.compactGram_special_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:41:39.800898+00:00
-- url     : https://prove2.me/submissions/d02e2989-1c66-412a-a64f-7a42652ba2a8

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
theorem _root_.solution (q : ℝ) (hq : 1 < q) :
    dotProduct (specialVector q) ((compactGram q).mulVec (specialVector q)) = q⁻¹ := by
  have hq0 : q ≠ 0 := by linarith
  have hq1 : q + 1 ≠ 0 := by linarith
  simp [specialVector, compactGram, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  field_simp
end FourierJacobi
