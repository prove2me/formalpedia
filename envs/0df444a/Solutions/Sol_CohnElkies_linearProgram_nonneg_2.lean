-- Prove2me | solution 2 for CohnElkies.linearProgram_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:01:01.808099+00:00
-- url     : https://prove2.me/submissions/2a0dd004-53f1-4801-bb45-3f3575f9c274

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter
open scoped Topology


theorem solution (d : ℕ) : 0 ≤ linearProgram d := by
  unfold linearProgram
  refine mul_nonneg (div_nonneg (unitBallVolume_pos d).le (by positivity)) (Real.sInf_nonneg ?_)
  rintro q ⟨f, rfl⟩
  exact (div_pos (admissible_zero_pos f) f.fourier_zero_pos).le

