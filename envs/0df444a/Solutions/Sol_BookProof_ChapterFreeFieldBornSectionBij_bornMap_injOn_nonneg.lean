-- Prove2me | solution 1 for BookProof.ChapterFreeFieldBornSectionBij.bornMap_injOn_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T04:32:41.401004+00:00
-- url     : https://prove2.me/submissions/067464e0-0cf7-473f-86b2-18542c613959

import Mathlib
import Definitions.Def_ChapterFreeFieldGaussian
import Definitions.Def_ChapterFreeFieldSphere
import Definitions.Def_ChapterFreeFieldSphereSupport
import Definitions.Def_ChapterFreeFieldBorn
import Definitions.Def_ChapterFreeFieldBornSurj
import Definitions.Def_ChapterFreeFieldBornSectionBij

set_option autoImplicit false

open MeasureTheory in
open BookProof.ChapterFreeFieldBornSectionBij BookProof.ChapterFreeFieldGaussian BookProof.ChapterFreeFieldSphere BookProof.ChapterFreeFieldSphereSupport BookProof.ChapterFreeFieldBorn BookProof.ChapterFreeFieldBornSurj in
theorem solution {n : ℕ} :
    Set.InjOn (bornMap : EuclideanSpace ℝ (Fin n) → _) (nonnegOrthant n) := by
  intro x hx y hy hxy
  ext k
  have h := congrFun hxy k
  simp only [bornMap] at h
  exact (sq_eq_sq₀ (hx k) (hy k)).1 h
