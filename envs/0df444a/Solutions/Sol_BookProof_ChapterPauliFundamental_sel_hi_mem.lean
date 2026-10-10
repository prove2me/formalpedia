-- Prove2me | solution 1 for BookProof.ChapterPauliFundamental.sel_hi_mem
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T09:36:09.668914+00:00
-- url     : https://prove2.me/submissions/bf5764a5-9e22-48ab-b2f1-905d5867a6a2

-- Generated from ChapterPauliFundamental.lean — solution of BookProof.ChapterPauliFundamental.sel_hi_mem
import Mathlib
import Definitions.Def_ChapterPauliFundamental
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterGammaCommutant
open BookProof.ChapterPauliFundamental



open Matrix Finset


open BookProof.ChapterA3 BookProof.ChapterGammaCommutant

variable {A : Fin 4 → M4}

set_option maxHeartbeats 1000000 in
theorem solution : ∀ (μ : Fin 4) (T : Finset (Fin 4)), μ ∈ T →
    sel (hi μ T) = μ :: sel (hi μ (T.erase μ)) := by
 decide
