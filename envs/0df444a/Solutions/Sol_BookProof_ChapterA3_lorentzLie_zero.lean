-- Prove2me | solution 1 for BookProof.ChapterA3.lorentzLie_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:08:06.794002+00:00
-- url     : https://prove2.me/submissions/6351ca13-6cce-4142-9465-52f51d9b4ee4

-- Generated from ChapterA3e.lean — solution of BookProof.ChapterA3.lorentzLie_zero
import Mathlib
import Definitions.Def_ChapterA3e
open BookProof.ChapterA3



open Matrix

set_option maxHeartbeats 1000000 in
theorem solution : (0 : Matrix (Fin 4) (Fin 4) ℝ) ∈ LorentzLie := by

  simp [LorentzLie]
