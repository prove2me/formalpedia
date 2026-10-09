-- Prove2me | solution 1 for BookProof.ChapterB4.mixed_state_isDensityMatrix
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T19:26:27.197979+00:00
-- url     : https://prove2.me/submissions/8488350d-446d-4e10-8659-99362efe2f62

-- Generated from ChapterB4.lean — solution of BookProof.ChapterB4.mixed_state_isDensityMatrix
import Mathlib
import Definitions.Def_ChapterB4
open BookProof.ChapterB4




open Matrix

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution :
    IsDensityMatrix ((1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) := by

  have hpsd : ((1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)).PosSemidef :=
    Matrix.PosSemidef.one.smul (by norm_num)
  refine ⟨hpsd.1, hpsd, ?_⟩
  norm_num [Matrix.trace_fin_two, Matrix.one_apply]
