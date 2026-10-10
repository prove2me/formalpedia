-- Prove2me | solution 1 for BookProof.IrreversibleDynamics.dissipative_nonsingular
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:18:38.389353+00:00
-- url     : https://prove2.me/submissions/1176b63c-3665-40b5-80be-1d09ab20f328

-- Generated from ChapterIrreversibleDynamics.lean — solution of BookProof.IrreversibleDynamics.dissipative_nonsingular
import Mathlib
import Definitions.Def_ChapterIrreversibleDynamics
import Theorems.Thm_BookProof_IrreversibleDynamics_dissipative_volume_image
open BookProof.IrreversibleDynamics




open MeasureTheory Function Set
open scoped ENNReal

set_option maxHeartbeats 1000000 in
theorem solution {A : Set ℝ} (h : 0 < volume A) :
    0 < volume (dissipative '' A) := by

  rw [dissipative_volume_image]
  simp [ENNReal.div_pos_iff, h.ne']
