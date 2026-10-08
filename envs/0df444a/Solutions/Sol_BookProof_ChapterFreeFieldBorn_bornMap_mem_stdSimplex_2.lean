-- Prove2me | solution 2 for BookProof.ChapterFreeFieldBorn.bornMap_mem_stdSimplex
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T07:36:20.621982+00:00
-- url     : https://prove2.me/submissions/4941f369-8e27-4093-9c02-e02f4a8f6060

import Definitions.Def_ChapterFreeFieldGaussian
import Definitions.Def_ChapterFreeFieldSphere
import Definitions.Def_ChapterFreeFieldSphereSupport
import Mathlib
import Definitions.Def_ChapterFreeFieldBorn

open MeasureTheory BookProof.ChapterFreeFieldGaussian BookProof.ChapterFreeFieldSphere BookProof.ChapterFreeFieldSphereSupport BookProof.ChapterFreeFieldBorn in
theorem solution {n : ℕ} {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    bornMap x ∈ stdSimplex ℝ (Fin n) := by
  have h1 : ‖x‖ = 1 := by simpa using hx
  have h2 : ‖x‖ ^ 2 = ∑ k, ‖x k‖ ^ 2 := EuclideanSpace.norm_sq_eq x
  rw [h1] at h2
  simp only [Real.norm_eq_abs, sq_abs] at h2
  refine ⟨fun k => sq_nonneg (x k), ?_⟩
  simp only [bornMap]
  linarith
