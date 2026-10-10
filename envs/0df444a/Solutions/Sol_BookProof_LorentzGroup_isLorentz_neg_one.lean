-- Prove2me | solution 1 for BookProof.LorentzGroup.isLorentz_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:43:43.65226+00:00
-- url     : https://prove2.me/submissions/b7055fd8-3680-416a-8475-cdfa703f6e6d

-- Generated from ChapterLorentzGroup.lean — solution of BookProof.LorentzGroup.isLorentz_neg_one
import Mathlib
import Definitions.Def_ChapterLorentzGroup
open BookProof.LorentzGroup




open Matrix

set_option maxHeartbeats 1000000 in
theorem solution : IsLorentz (-1 : Matrix (Fin 4) (Fin 4) ℝ) := by

  -- By definition of IsLorentz, we need to show that (-1)ᵀ * eta * (-1) = eta.
  simp [IsLorentz]
