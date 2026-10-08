-- Prove2me | solution 1 for BookProof.ChapterFreeFieldSphere.sphereGaussian_map_linearIsometryEquiv
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-05T09:23:17.351005+00:00
-- url     : https://prove2.me/submissions/df5bdf52-9dc3-4821-833d-75ded59dd674

-- Generated from ChapterFreeFieldSphere.lean — solution of BookProof.ChapterFreeFieldSphere.sphereGaussian_map_linearIsometryEquiv
import Mathlib
import Definitions.Def_ChapterFreeFieldSphere
import Theorems.Thm_BookProof_ChapterFreeFieldSphere_normalize_comm
import Theorems.Thm_BookProof_ChapterFreeFieldGaussian_stdGaussian_map_linearIsometryEquiv
open BookProof.ChapterFreeFieldSphere



open MeasureTheory
open BookProof.ChapterFreeFieldGaussian


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution
    (L : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    (sphereGaussian n).map L = sphereGaussian n := by

  -- By definition of `sphereGaussian`, we have `(sphereGaussian n).map L = ((stdGaussian n).map
  -- normalize).map L`.
  rw [show sphereGaussian n = (stdGaussian n).map normalize from rfl];
  rw [ MeasureTheory.Measure.map_map, show L ∘ normalize = normalize ∘ L from ?_ ];
  · rw [ ← MeasureTheory.Measure.map_map, stdGaussian_map_linearIsometryEquiv ];
    · exact measurable_normalize;
    · exact L.continuous.measurable;
  · funext x; exact (normalize_comm L x).symm
  · exact L.continuous.measurable;
  · exact measurable_normalize
