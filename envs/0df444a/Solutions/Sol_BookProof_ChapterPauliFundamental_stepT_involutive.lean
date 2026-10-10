-- Prove2me | solution 1 for BookProof.ChapterPauliFundamental.stepT_involutive
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T09:36:13.853823+00:00
-- url     : https://prove2.me/submissions/320b5c3a-0ddb-494b-b71b-8c99a87bd1eb

-- Generated from ChapterPauliFundamental.lean — solution of BookProof.ChapterPauliFundamental.stepT_involutive
import Mathlib
import Definitions.Def_ChapterPauliFundamental
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterGammaCommutant
open BookProof.ChapterPauliFundamental



open Matrix Finset


open BookProof.ChapterA3 BookProof.ChapterGammaCommutant

variable {A : Fin 4 → M4}

set_option maxHeartbeats 1000000 in
theorem solution : ∀ (μ : Fin 4) (T : Finset (Fin 4)), stepT μ (stepT μ T) = T := by

  decide
