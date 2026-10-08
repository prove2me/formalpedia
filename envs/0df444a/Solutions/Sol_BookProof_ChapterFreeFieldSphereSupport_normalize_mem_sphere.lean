-- Prove2me | solution 1 for BookProof.ChapterFreeFieldSphereSupport.normalize_mem_sphere
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T16:49:32.655542+00:00
-- url     : https://prove2.me/submissions/6ad91de5-459d-41fe-8cc6-8882c0191c5d

import Mathlib
import Definitions.Def_ChapterFreeFieldGaussian
import Definitions.Def_ChapterFreeFieldSphere
import Definitions.Def_ChapterFreeFieldSphereSupport

open BookProof.ChapterFreeFieldSphereSupport MeasureTheory ProbabilityTheory BookProof.ChapterFreeFieldGaussian BookProof.ChapterFreeFieldSphere in
theorem solution {n : ℕ} {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) :
    normalize x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
  rw [mem_sphere_zero_iff_norm]
  show ‖‖x‖⁻¹ • x‖ = 1
  rw [norm_smul, norm_inv, norm_norm]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)
