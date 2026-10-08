-- Prove2me | solution 1 for BookProof.ChapterFreeFieldBornSurj.bornSection_mem_sphere
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-05T10:04:05.42651+00:00
-- url     : https://prove2.me/submissions/2741ed63-d1d6-42c0-af02-d2fd0990e9b0

-- Generated from ChapterFreeFieldBornSurj.lean — solution of BookProof.ChapterFreeFieldBornSurj.bornSection_mem_sphere
import Mathlib
import Definitions.Def_ChapterFreeFieldBornSurj
import Theorems.Thm_BookProof_ChapterFreeFieldBornSurj_bornSection_apply
open BookProof.ChapterFreeFieldBornSurj



open MeasureTheory
open BookProof.ChapterFreeFieldGaussian BookProof.ChapterFreeFieldSphere
open BookProof.ChapterFreeFieldSphereSupport BookProof.ChapterFreeFieldBorn


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {p : Fin n → ℝ} (hp : p ∈ stdSimplex ℝ (Fin n)) :
    bornSection p ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by

  rw [Metric.mem_sphere, dist_zero_right, EuclideanSpace.norm_eq, Real.sqrt_eq_one, ← hp.2]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Real.norm_eq_abs, sq_abs, bornSection_apply, Real.sq_sqrt (hp.1 i)]
