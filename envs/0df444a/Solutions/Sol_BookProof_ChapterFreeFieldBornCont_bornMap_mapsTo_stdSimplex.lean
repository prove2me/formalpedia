-- Prove2me | solution 1 for BookProof.ChapterFreeFieldBornCont.bornMap_mapsTo_stdSimplex
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-05T10:04:29.613877+00:00
-- url     : https://prove2.me/submissions/74679a85-ff41-43c6-8af5-3720d7fce4ff

-- Generated from ChapterFreeFieldBornCont.lean — solution of BookProof.ChapterFreeFieldBornCont.bornMap_mapsTo_stdSimplex
import Mathlib
import Definitions.Def_ChapterFreeFieldBornCont
import Theorems.Thm_BookProof_ChapterFreeFieldBorn_bornMap_mem_stdSimplex
open BookProof.ChapterFreeFieldBornCont



open MeasureTheory
open BookProof.ChapterFreeFieldBorn BookProof.ChapterFreeFieldBornSurj


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution :
    Set.MapsTo (bornMap : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ))
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) (stdSimplex ℝ (Fin n)) := fun _ hx => bornMap_mem_stdSimplex hx
