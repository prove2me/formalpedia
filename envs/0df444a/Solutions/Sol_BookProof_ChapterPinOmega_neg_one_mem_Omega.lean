-- Prove2me | solution 1 for BookProof.ChapterPinOmega.neg_one_mem_Omega
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T10:00:19.917983+00:00
-- url     : https://prove2.me/submissions/17429604-90c6-45fb-bd04-2672e51e567a

-- Generated from ChapterPinOmega.lean — solution of BookProof.ChapterPinOmega.neg_one_mem_Omega
import Mathlib
import Definitions.Def_ChapterPinOmega
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterPinDoubleCover
open BookProof.ChapterPinOmega



open Matrix


open BookProof.ChapterA3

set_option maxHeartbeats 1000000 in
theorem solution : (-1 : Matrix (Fin 4) (Fin 4) ℤ) ∈ Omega := by
 decide
