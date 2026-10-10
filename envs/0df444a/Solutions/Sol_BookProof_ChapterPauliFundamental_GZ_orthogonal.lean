-- Prove2me | solution 1 for BookProof.ChapterPauliFundamental.GZ_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T09:36:17.114959+00:00
-- url     : https://prove2.me/submissions/6cab7891-ce04-4777-a7b7-e2c2bbda3bee

-- Generated from ChapterPauliFundamental.lean — solution of BookProof.ChapterPauliFundamental.GZ_orthogonal
import Mathlib
import Definitions.Def_ChapterPauliFundamental
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterGammaCommutant
open BookProof.ChapterPauliFundamental



open Matrix Finset


open BookProof.ChapterA3 BookProof.ChapterGammaCommutant

variable {A : Fin 4 → M4}

set_option maxHeartbeats 1000000 in
theorem solution : ∀ T : Finset (Fin 4), GZ T * (GZ T)ᵀ = 1 := by
 decide
