-- Prove2me | solution 1 for BookProof.IrreversibleDynamics.dissipative_nonsingular_Icc
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:18:24.03961+00:00
-- url     : https://prove2.me/submissions/df40870d-198f-4bbc-9492-6a969360a133

-- Generated from ChapterIrreversibleDynamics.lean — solution of BookProof.IrreversibleDynamics.dissipative_nonsingular_Icc
import Mathlib
import Definitions.Def_ChapterIrreversibleDynamics
import Theorems.Thm_BookProof_IrreversibleDynamics_dissipative_volume_Icc
open BookProof.IrreversibleDynamics




open MeasureTheory Function Set
open scoped ENNReal

set_option maxHeartbeats 1000000 in
theorem solution {a b : ℝ} (h : a < b) :
    0 < volume (dissipative '' Set.Icc a b) := by

  rw [dissipative_volume_Icc]
  simp only [ENNReal.ofReal_pos]
  linarith
