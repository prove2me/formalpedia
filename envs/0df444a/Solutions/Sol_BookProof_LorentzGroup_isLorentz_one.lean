-- Prove2me | solution 1 for BookProof.LorentzGroup.isLorentz_one
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:42:01.107638+00:00
-- url     : https://prove2.me/submissions/7a2197ef-13bc-4d45-b496-17404468ab6e

-- Generated from ChapterLorentzGroup.lean — solution of BookProof.LorentzGroup.isLorentz_one
import Mathlib
import Definitions.Def_ChapterLorentzGroup
open BookProof.LorentzGroup




open Matrix

set_option maxHeartbeats 1000000 in
theorem solution : IsLorentz 1 := by

  -- By definition of IsLorentz, we need to show that 1^T * eta * 1 = eta.
  simp [IsLorentz]
