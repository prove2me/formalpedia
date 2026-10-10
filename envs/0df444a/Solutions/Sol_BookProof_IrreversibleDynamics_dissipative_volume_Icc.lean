-- Prove2me | solution 1 for BookProof.IrreversibleDynamics.dissipative_volume_Icc
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:18:12.323567+00:00
-- url     : https://prove2.me/submissions/3fcfc5c1-e95d-4fba-98fb-6c5ca8e7a61c

-- Generated from ChapterIrreversibleDynamics.lean — solution of BookProof.IrreversibleDynamics.dissipative_volume_Icc
import Mathlib
import Definitions.Def_ChapterIrreversibleDynamics
import Theorems.Thm_BookProof_IrreversibleDynamics_dissipative_image_Icc
open BookProof.IrreversibleDynamics




open MeasureTheory Function Set
open scoped ENNReal

set_option maxHeartbeats 1000000 in
theorem solution (a b : ℝ) :
    volume (dissipative '' Set.Icc a b) = ENNReal.ofReal ((b - a) / 2) := by

  rw [dissipative_image_Icc, Real.volume_Icc]
  congr 1; ring
