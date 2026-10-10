-- Prove2me | solution 1 for BookProof.ChapterPauliFundamental.lo_stepT
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T09:36:11.800804+00:00
-- url     : https://prove2.me/submissions/7157d86c-59a0-4995-aab7-ee529c210cff

-- Generated from ChapterPauliFundamental.lean — solution of BookProof.ChapterPauliFundamental.lo_stepT
import Mathlib
import Definitions.Def_ChapterPauliFundamental
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterGammaCommutant
open BookProof.ChapterPauliFundamental



open Matrix Finset


open BookProof.ChapterA3 BookProof.ChapterGammaCommutant

variable {A : Fin 4 → M4}

set_option maxHeartbeats 1000000 in
theorem solution : ∀ (μ : Fin 4) (T : Finset (Fin 4)), lo μ (stepT μ T) = lo μ T := by
 decide
