-- Prove2me | solution 1 for BookProof.ChapterPauliFundamental.sel_hi_insert
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T09:36:10.708762+00:00
-- url     : https://prove2.me/submissions/beac9cec-07ad-4786-ac84-06155dc6fdf5

-- Generated from ChapterPauliFundamental.lean — solution of BookProof.ChapterPauliFundamental.sel_hi_insert
import Mathlib
import Definitions.Def_ChapterPauliFundamental
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterGammaCommutant
open BookProof.ChapterPauliFundamental



open Matrix Finset


open BookProof.ChapterA3 BookProof.ChapterGammaCommutant

variable {A : Fin 4 → M4}

set_option maxHeartbeats 1000000 in
theorem solution : ∀ (μ : Fin 4) (T : Finset (Fin 4)), μ ∉ T →
    sel (hi μ (insert μ T)) = μ :: sel (hi μ T) := by
 decide
