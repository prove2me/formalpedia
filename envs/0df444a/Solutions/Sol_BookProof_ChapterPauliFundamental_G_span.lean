-- Prove2me | solution 1 for BookProof.ChapterPauliFundamental.G_span
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T09:36:26.420706+00:00
-- url     : https://prove2.me/submissions/8dfb6e49-6bd6-4b99-9764-30cd507d7ef9

-- Generated from ChapterPauliFundamental.lean — solution of BookProof.ChapterPauliFundamental.G_span
import Mathlib
import Definitions.Def_ChapterPauliFundamental
import Theorems.Thm_BookProof_ChapterPauliFundamental_G_linearIndependent
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterGammaCommutant
open BookProof.ChapterPauliFundamental



open Matrix Finset


open BookProof.ChapterA3 BookProof.ChapterGammaCommutant

variable {A : Fin 4 → M4}

set_option maxHeartbeats 1000000 in
theorem solution : Submodule.span ℂ (Set.range G) = ⊤ := by

  have hcard : Fintype.card (Finset (Fin 4)) = Module.finrank ℂ M4 := by
    rw [Module.finrank_matrix]
    simp
  have := (basisOfLinearIndependentOfCardEqFinrank G_linearIndependent hcard).span_eq
  rwa [coe_basisOfLinearIndependentOfCardEqFinrank] at this
