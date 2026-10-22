-- Prove2me | solution 1 for BookProof.LimitCircleExample.memLp_lcSol
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-21T12:16:28.945118+00:00
-- url     : https://prove2.me/submissions/640104cc-b991-4222-8c13-6c8a65a54a23

-- Generated from ChapterLimitCircleExample.lean — solution of BookProof.LimitCircleExample.memLp_lcSol
import Mathlib
import Definitions.Def_ChapterLimitCircleExample
import Theorems.Thm_BookProof_LimitCircleExample_lcSol_sq_le
import Theorems.Thm_BookProof_LimitCircleExample_continuous_lcSol
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
theorem solution : MemLp lcSol 2 (volume : Measure ℝ) := by

  refine (memLp_two_iff_integrable_sq_norm
    continuous_lcSol.aestronglyMeasurable).2 ?_
  have hg : Integrable (fun x : ℝ => Real.exp π * (1 + x ^ 2)⁻¹) volume :=
    integrable_inv_one_add_sq.const_mul _
  refine Integrable.mono' hg ((continuous_lcSol.norm.pow 2).aestronglyMeasurable) ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact lcSol_sq_le x
