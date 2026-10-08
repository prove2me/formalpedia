-- Prove2me | solution 2 for BookProof.ChapterFreeFieldBornCont.bornMap_mapsTo_stdSimplex
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T06:47:51.250247+00:00
-- url     : https://prove2.me/submissions/28e5fc83-8809-4407-8587-23a1eb02931c

import Definitions.Def_ChapterFreeFieldBorn
import Definitions.Def_ChapterFreeFieldBornSurj
import Mathlib
import Definitions.Def_ChapterFreeFieldBornCont

open MeasureTheory BookProof.ChapterFreeFieldBornCont BookProof.ChapterFreeFieldBorn BookProof.ChapterFreeFieldBornSurj in
theorem solution {n : ℕ} :
    Set.MapsTo (bornMap : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ))
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) (stdSimplex ℝ (Fin n)) := by
  intro x hx
  have h1 : ‖x‖ = 1 := by simpa using hx
  have h2 : ‖x‖ ^ 2 = ∑ k, ‖x k‖ ^ 2 := EuclideanSpace.norm_sq_eq x
  rw [h1] at h2
  simp only [Real.norm_eq_abs, sq_abs] at h2
  refine ⟨fun k => sq_nonneg (x k), ?_⟩
  simp only [bornMap]
  linarith
