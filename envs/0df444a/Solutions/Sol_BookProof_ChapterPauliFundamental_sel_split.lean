-- Prove2me | solution 1 for BookProof.ChapterPauliFundamental.sel_split
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T09:36:08.547618+00:00
-- url     : https://prove2.me/submissions/0d2985e7-18d2-46c6-b8b9-dcbccfd62d3e

-- Generated from ChapterPauliFundamental.lean — solution of BookProof.ChapterPauliFundamental.sel_split
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
    sel T = sel (lo μ T) ++ sel (hi μ T) := by
 decide
