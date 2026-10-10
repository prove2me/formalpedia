-- Prove2me | solution 1 for BookProof.ChapterPauliFundamental.GZ_traceOrth
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T09:36:18.249955+00:00
-- url     : https://prove2.me/submissions/2209c21f-4119-41f7-ad48-c351eaaed28b

-- Generated from ChapterPauliFundamental.lean — solution of BookProof.ChapterPauliFundamental.GZ_traceOrth
import Mathlib
import Definitions.Def_ChapterPauliFundamental
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterGammaCommutant
open BookProof.ChapterPauliFundamental



open Matrix Finset


open BookProof.ChapterA3 BookProof.ChapterGammaCommutant

variable {A : Fin 4 → M4}

set_option maxHeartbeats 1000000 in
theorem solution : ∀ S T : Finset (Fin 4),
    (GZ S * (GZ T)ᵀ).trace = if S = T then 4 else 0 := by
 decide
