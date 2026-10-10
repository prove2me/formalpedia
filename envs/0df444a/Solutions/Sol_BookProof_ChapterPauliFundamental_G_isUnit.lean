-- Prove2me | solution 1 for BookProof.ChapterPauliFundamental.G_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T09:36:22.770073+00:00
-- url     : https://prove2.me/submissions/0f52f384-3cd8-4fc4-bf91-f8a9c66a42b6

-- Generated from ChapterPauliFundamental.lean — solution of BookProof.ChapterPauliFundamental.G_isUnit
import Mathlib
import Definitions.Def_ChapterPauliFundamental
import Theorems.Thm_BookProof_ChapterPauliFundamental_G_orthogonal
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterGammaCommutant
open BookProof.ChapterPauliFundamental



open Matrix Finset


open BookProof.ChapterA3 BookProof.ChapterGammaCommutant

variable {A : Fin 4 → M4}

set_option maxHeartbeats 1000000 in
theorem solution (T : Finset (Fin 4)) : IsUnit (G T).det := Matrix.isUnit_det_of_right_inverse (G_orthogonal T)
