-- Prove2me | solution 1 for BookProof.ChapterFreeFieldBornCont.stdSimplex_eq_bornMap_image_sphere
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-05T10:05:13.051852+00:00
-- url     : https://prove2.me/submissions/109d14c8-4635-4e3c-9187-2b8c5baf699b

-- Generated from ChapterFreeFieldBornCont.lean — solution of BookProof.ChapterFreeFieldBornCont.stdSimplex_eq_bornMap_image_sphere
import Mathlib
import Definitions.Def_ChapterFreeFieldBornCont
import Theorems.Thm_BookProof_ChapterFreeFieldBornSurj_bornMap_surjOn_stdSimplex
import Theorems.Thm_BookProof_ChapterFreeFieldBorn_bornMap_mem_stdSimplex
open BookProof.ChapterFreeFieldBornCont



open MeasureTheory
open BookProof.ChapterFreeFieldBorn BookProof.ChapterFreeFieldBornSurj


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution :
    stdSimplex ℝ (Fin n) =
      (bornMap : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ)) ''
        (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) := by

  apply Set.Subset.antisymm
  · exact bornMap_surjOn_stdSimplex
  · rintro _ ⟨x, hx, rfl⟩
    exact bornMap_mem_stdSimplex hx
