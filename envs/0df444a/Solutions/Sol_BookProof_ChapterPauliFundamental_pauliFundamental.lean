-- Prove2me | solution 1 for BookProof.ChapterPauliFundamental.pauliFundamental
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T09:36:33.604605+00:00
-- url     : https://prove2.me/submissions/0401ac1c-0611-4461-8fca-653daf678a07
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterPauliFundamental.lean — solution of BookProof.ChapterPauliFundamental.pauliFundamental
import Mathlib
import Definitions.Def_ChapterPauliFundamental
import Theorems.Thm_BookProof_ChapterPauliFundamental_pauli_exists
import Theorems.Thm_BookProof_ChapterPauliFundamental_pauli_unique
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterGammaCommutant
import Definitions.Def_ChapterA3b
open BookProof.ChapterPauliFundamental



open Matrix Finset


open BookProof.ChapterA3 BookProof.ChapterGammaCommutant

variable {A : Fin 4 → M4}

set_option maxHeartbeats 1000000 in
theorem solution : PauliFundamental := by

  intro A B hA hB
  exact ⟨pauli_exists hA hB, fun S T hS hT hSeq hTeq => pauli_unique hA S T hS hT hSeq hTeq⟩
