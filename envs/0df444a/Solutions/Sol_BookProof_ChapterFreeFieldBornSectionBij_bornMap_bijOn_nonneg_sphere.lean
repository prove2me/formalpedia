-- Prove2me | solution 1 for BookProof.ChapterFreeFieldBornSectionBij.bornMap_bijOn_nonneg_sphere
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-05T10:54:49.966139+00:00
-- url     : https://prove2.me/submissions/250435e0-6e17-455d-875e-5cdf58e56b77

-- Generated from ChapterFreeFieldBornSectionBij.lean — solution of BookProof.ChapterFreeFieldBornSectionBij.bornMap_bijOn_nonneg_sphere
import Mathlib
import Definitions.Def_ChapterFreeFieldBornSectionBij
import Theorems.Thm_BookProof_ChapterFreeFieldBornSectionBij_bornSection_nonneg
import Theorems.Thm_BookProof_ChapterFreeFieldBornSectionBij_bornMap_injOn_nonneg
import Theorems.Thm_BookProof_ChapterFreeFieldBornSurj_bornMap_bornSection
import Theorems.Thm_BookProof_ChapterFreeFieldBornSurj_bornSection_mem_sphere
import Theorems.Thm_BookProof_ChapterFreeFieldBorn_bornMap_mem_stdSimplex
open BookProof.ChapterFreeFieldBornSectionBij



open MeasureTheory
open BookProof.ChapterFreeFieldGaussian BookProof.ChapterFreeFieldSphere
open BookProof.ChapterFreeFieldSphereSupport BookProof.ChapterFreeFieldBorn
open BookProof.ChapterFreeFieldBornSurj


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution :
    Set.BijOn (bornMap : EuclideanSpace ℝ (Fin n) → _)
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ∩ nonnegOrthant n)
      (stdSimplex ℝ (Fin n)) := by

  refine ⟨?_, ?_, ?_⟩
  · -- MapsTo
    intro x hx
    exact bornMap_mem_stdSimplex hx.1
  · -- InjOn
    exact bornMap_injOn_nonneg.mono (Set.inter_subset_right)
  · -- SurjOn
    intro p hp
    exact ⟨bornSection p, ⟨bornSection_mem_sphere hp, bornSection_nonneg p⟩,
      bornMap_bornSection hp⟩
