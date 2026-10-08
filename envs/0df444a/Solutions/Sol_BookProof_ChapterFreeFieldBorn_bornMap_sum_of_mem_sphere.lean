-- Prove2me | solution 1 for BookProof.ChapterFreeFieldBorn.bornMap_sum_of_mem_sphere
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T08:33:45.494079+00:00
-- url     : https://prove2.me/submissions/7d4f099f-dfc6-4133-b1cf-7112e47eaeaf

import Definitions.Def_ChapterFreeFieldGaussian
import Definitions.Def_ChapterFreeFieldSphere
import Definitions.Def_ChapterFreeFieldSphereSupport
import Mathlib
import Definitions.Def_ChapterFreeFieldBorn

open MeasureTheory BookProof.ChapterFreeFieldGaussian BookProof.ChapterFreeFieldSphere BookProof.ChapterFreeFieldSphereSupport BookProof.ChapterFreeFieldBorn in
theorem solution {n : ℕ} {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    ∑ k, bornMap x k = 1 := by
  have h1 : ‖x‖ = 1 := by simpa using hx
  have h2 : ‖x‖ ^ 2 = ∑ k, ‖x k‖ ^ 2 := EuclideanSpace.norm_sq_eq x
  simp only [bornMap]
  rw [h1] at h2
  simp only [Real.norm_eq_abs, sq_abs] at h2
  linarith
