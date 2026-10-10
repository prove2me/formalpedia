-- Prove2me | solution 1 for BookProof.ChapterPauliFundamental.inter_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T09:36:31.79161+00:00
-- url     : https://prove2.me/submissions/91739b56-909e-4230-a2e0-a94600760d81

-- Generated from ChapterPauliFundamental.lean — solution of BookProof.ChapterPauliFundamental.inter_isUnit
import Mathlib
import Definitions.Def_ChapterPauliFundamental
import Theorems.Thm_BookProof_ChapterPauliFundamental_inter_intertwines
import Theorems.Thm_BookProof_ChapterPauliFundamental_intertwiner_isUnit
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterGammaCommutant
import Definitions.Def_ChapterA3b
open BookProof.ChapterPauliFundamental



open Matrix Finset


open BookProof.ChapterA3 BookProof.ChapterGammaCommutant

variable {A : Fin 4 → M4}

set_option maxHeartbeats 1000000 in
theorem solution (hA : IsCliffordC A) {F : M4} (hF : inter A F ≠ 0) :
    IsUnit (inter A F).det := intertwiner_isUnit hF (fun μ => inter_intertwines hA F μ)
