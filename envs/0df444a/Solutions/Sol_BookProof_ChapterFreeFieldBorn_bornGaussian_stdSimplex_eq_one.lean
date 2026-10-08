-- Prove2me | solution 1 for BookProof.ChapterFreeFieldBorn.bornGaussian_stdSimplex_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-05T09:41:59.903189+00:00
-- url     : https://prove2.me/submissions/f3270fa6-cd47-4a26-8e8e-dcf8311b6143

-- Generated from ChapterFreeFieldBorn.lean — solution of BookProof.ChapterFreeFieldBorn.bornGaussian_stdSimplex_eq_one
import Mathlib
import Definitions.Def_ChapterFreeFieldBorn
import Theorems.Thm_BookProof_ChapterFreeFieldBorn_measurable_bornMap
import Theorems.Thm_BookProof_ChapterFreeFieldBorn_bornMap_mem_stdSimplex
import Theorems.Thm_BookProof_ChapterFreeFieldSphereSupport_sphereGaussian_sphere_eq_one
open BookProof.ChapterFreeFieldBorn



open MeasureTheory
open BookProof.ChapterFreeFieldGaussian BookProof.ChapterFreeFieldSphere
open BookProof.ChapterFreeFieldSphereSupport


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (hn : 0 < n) :
    ((sphereGaussian n).map bornMap) (stdSimplex ℝ (Fin n)) = 1 := by

  rw [Measure.map_apply measurable_bornMap (isClosed_stdSimplex ℝ (Fin n)).measurableSet]
  refine le_antisymm prob_le_one ?_
  calc (1 : ENNReal)
      = sphereGaussian n (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :=
        (sphereGaussian_sphere_eq_one hn).symm
    _ ≤ sphereGaussian n (bornMap ⁻¹' stdSimplex ℝ (Fin n)) := by
        apply measure_mono
        intro x hx
        exact bornMap_mem_stdSimplex hx
