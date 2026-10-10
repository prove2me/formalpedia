-- Prove2me | solution 1 for BookProof.ChapterPinOmega.one_mem_Omega
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T10:00:18.883056+00:00
-- url     : https://prove2.me/submissions/56a6789b-6689-4f97-8488-7ac59a90e9ba

-- Generated from ChapterPinOmega.lean — solution of BookProof.ChapterPinOmega.one_mem_Omega
import Mathlib
import Definitions.Def_ChapterPinOmega
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterPinDoubleCover
open BookProof.ChapterPinOmega



open Matrix


open BookProof.ChapterA3

set_option maxHeartbeats 1000000 in
theorem solution : (1 : Matrix (Fin 4) (Fin 4) ℤ) ∈ Omega := by
 decide
