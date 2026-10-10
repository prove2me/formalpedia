-- Prove2me | solution 1 for BookProof.LorentzGroup.eta_transpose
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:41:04.032272+00:00
-- url     : https://prove2.me/submissions/45637ed0-8f0b-43f2-a88a-4e565cdf9e71

-- Generated from ChapterLorentzGroup.lean — solution of BookProof.LorentzGroup.eta_transpose
import Mathlib
import Definitions.Def_ChapterLorentzGroup
open BookProof.LorentzGroup




open Matrix

set_option maxHeartbeats 1000000 in
theorem solution : etaᵀ = eta := by

  ext i j; fin_cases i <;> fin_cases j <;> rfl;
