-- Prove2me | solution 1 for BookProof.ChapterFreeFieldBorn.bornMap_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T16:49:16.474034+00:00
-- url     : https://prove2.me/submissions/e0741055-83c1-4f0f-ab73-44b05b17c18c

import Mathlib
import Definitions.Def_ChapterFreeFieldGaussian
import Definitions.Def_ChapterFreeFieldSphere
import Definitions.Def_ChapterFreeFieldSphereSupport
import Definitions.Def_ChapterFreeFieldBorn

set_option autoImplicit false

open BookProof.ChapterFreeFieldBorn MeasureTheory BookProof.ChapterFreeFieldGaussian BookProof.ChapterFreeFieldSphere BookProof.ChapterFreeFieldSphereSupport in
theorem solution {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (k : Fin n) : 0 ≤ bornMap x k := by
  unfold bornMap
  exact sq_nonneg _
