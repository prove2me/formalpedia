-- Prove2me | solution 1 for BookProof.LimitCircleExample.lcSol_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-21T12:16:04.8458+00:00
-- url     : https://prove2.me/submissions/654c84c4-1abd-4c97-b30a-18c50fb6a3ff

-- Generated from ChapterLimitCircleExample.lean — solution of BookProof.LimitCircleExample.lcSol_sq_le
import Mathlib
import Definitions.Def_ChapterLimitCircleExample
import Theorems.Thm_BookProof_LimitCircleExample_one_add_sq_pos
import Theorems.Thm_BookProof_LimitCircleExample_norm_lcSol
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterScalaronWallEsa
import Definitions.Def_ChapterWallDeficiencyObstruction
open BookProof.LimitCircleExample




open MeasureTheory Real
open BookProof.FarisLavine BookProof.ScalaronEsa BookProof.ScalaronWallEsa
open BookProof.WallDeficiencyObstruction

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (x : ℝ) : ‖lcSol x‖ ^ 2 ≤ Real.exp π * (1 + x ^ 2)⁻¹ := by

  have hpos : (0 : ℝ) < 1 + x ^ 2 := one_add_sq_pos x
  rw [norm_lcSol, ← Real.exp_nat_mul]
  have hstep : (2 : ℕ) * lcP x = 2 * Real.arctan x - Real.log (1 + x ^ 2) := by
    unfold lcP; push_cast; ring
  rw [hstep, Real.exp_sub, Real.exp_log hpos, div_eq_mul_inv]
  have h2 : Real.exp (2 * Real.arctan x) ≤ Real.exp π := by
    apply Real.exp_le_exp.2
    nlinarith [Real.arctan_lt_pi_div_two x]
  exact mul_le_mul_of_nonneg_right h2 (by positivity)
