-- Prove2me | solution 1 for BookProof.ChapterPauliFundamental.sel_lo_length
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T09:36:14.865272+00:00
-- url     : https://prove2.me/submissions/11f15155-6247-4f79-ba6c-710d324c24db

-- Generated from ChapterPauliFundamental.lean — solution of BookProof.ChapterPauliFundamental.sel_lo_length
import Mathlib
import Definitions.Def_ChapterPauliFundamental
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterGammaCommutant
open BookProof.ChapterPauliFundamental



open Matrix Finset


open BookProof.ChapterA3 BookProof.ChapterGammaCommutant

variable {A : Fin 4 → M4}

set_option maxHeartbeats 1000000 in
theorem solution : ∀ (μ : Fin 4) (T : Finset (Fin 4)),
    (sel (lo μ T)).length = (lo μ T).card := by
 decide
