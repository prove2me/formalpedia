-- Prove2me | solution 1 for BookProof.ChapterBell.chsh_quantum_value
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T19:27:51.11282+00:00
-- url     : https://prove2.me/submissions/fe26eb1f-ac5a-4905-94a0-9ac7acd2212e

-- Generated from ChapterBell.lean — solution of BookProof.ChapterBell.chsh_quantum_value
import Mathlib
import Definitions.Def_ChapterBell
open BookProof.ChapterBell



open scoped BigOperators
open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

set_option maxHeartbeats 1000000 in
theorem solution : chshValue = ((2 * Real.sqrt 2 : ℝ) : ℂ) := by

  have hne : (Real.sqrt 2 : ℂ) ≠ 0 := by simp
  have h2 : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by norm_cast; exact Real.sq_sqrt (by norm_num)
  unfold chshValue chshOp bellState A0 A1 B0 B1 sx sz
  simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
    Matrix.add_apply, Matrix.sub_apply, mul_comm]
  field_simp
  linear_combination (-2 * (Real.sqrt 2 : ℂ) ^ 2 - 4) * h2
