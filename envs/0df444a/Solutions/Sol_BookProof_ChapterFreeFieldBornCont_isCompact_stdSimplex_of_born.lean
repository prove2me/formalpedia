-- Prove2me | solution 1 for BookProof.ChapterFreeFieldBornCont.isCompact_stdSimplex_of_born
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-05T10:05:56.058709+00:00
-- url     : https://prove2.me/submissions/96061951-628b-4e35-9693-4c96fc949f7a

-- Generated from ChapterFreeFieldBornCont.lean — solution of BookProof.ChapterFreeFieldBornCont.isCompact_stdSimplex_of_born
import Mathlib
import Definitions.Def_ChapterFreeFieldBornCont
import Theorems.Thm_BookProof_ChapterFreeFieldBornCont_continuous_bornMap
import Theorems.Thm_BookProof_ChapterFreeFieldBornCont_stdSimplex_eq_bornMap_image_sphere
open BookProof.ChapterFreeFieldBornCont



open MeasureTheory
open BookProof.ChapterFreeFieldBorn BookProof.ChapterFreeFieldBornSurj


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution :
    IsCompact (stdSimplex ℝ (Fin n)) := by

  rw [stdSimplex_eq_bornMap_image_sphere]
  exact (isCompact_sphere (0 : EuclideanSpace ℝ (Fin n)) 1).image continuous_bornMap
