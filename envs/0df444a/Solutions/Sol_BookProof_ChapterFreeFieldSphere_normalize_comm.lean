-- Prove2me | solution 1 for BookProof.ChapterFreeFieldSphere.normalize_comm
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T20:13:39.576516+00:00
-- url     : https://prove2.me/submissions/03ed620b-52ce-4782-a915-09d226e57c99

import Mathlib
import Definitions.Def_ChapterFreeFieldGaussian
import Definitions.Def_ChapterFreeFieldSphere

set_option autoImplicit false

open BookProof.ChapterFreeFieldSphere MeasureTheory BookProof.ChapterFreeFieldGaussian in
theorem solution {n : ℕ} (L : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) : normalize (L x) = L (normalize x) := by
  unfold BookProof.ChapterFreeFieldSphere.normalize
  rw [LinearIsometryEquiv.norm_map, LinearIsometryEquiv.map_smul]
