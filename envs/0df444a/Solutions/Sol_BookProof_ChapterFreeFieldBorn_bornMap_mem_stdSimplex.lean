-- Prove2me | solution 1 for BookProof.ChapterFreeFieldBorn.bornMap_mem_stdSimplex
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-05T09:41:45.659574+00:00
-- url     : https://prove2.me/submissions/5e96f524-6605-4251-b824-f062d86ccc97

-- Generated from ChapterFreeFieldBorn.lean — solution of BookProof.ChapterFreeFieldBorn.bornMap_mem_stdSimplex
import Mathlib
import Definitions.Def_ChapterFreeFieldBorn
import Theorems.Thm_BookProof_ChapterFreeFieldBorn_bornMap_nonneg
import Theorems.Thm_BookProof_ChapterFreeFieldBorn_bornMap_sum_of_mem_sphere
open BookProof.ChapterFreeFieldBorn



open MeasureTheory
open BookProof.ChapterFreeFieldGaussian BookProof.ChapterFreeFieldSphere
open BookProof.ChapterFreeFieldSphereSupport


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    bornMap x ∈ stdSimplex ℝ (Fin n) := ⟨fun k => bornMap_nonneg x k, bornMap_sum_of_mem_sphere hx⟩
