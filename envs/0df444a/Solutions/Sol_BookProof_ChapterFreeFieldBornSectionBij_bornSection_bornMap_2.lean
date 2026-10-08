-- Prove2me | solution 2 for BookProof.ChapterFreeFieldBornSectionBij.bornSection_bornMap
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T00:51:03.915+00:00
-- url     : https://prove2.me/submissions/45a8052f-e7b4-4013-a03f-1dcd78c13cde

import Definitions.Def_ChapterFreeFieldGaussian
import Definitions.Def_ChapterFreeFieldSphere
import Definitions.Def_ChapterFreeFieldSphereSupport
import Definitions.Def_ChapterFreeFieldBorn
import Definitions.Def_ChapterFreeFieldBornSurj
import Mathlib
import Definitions.Def_ChapterFreeFieldBornSectionBij

set_option autoImplicit false

open MeasureTheory BookProof.ChapterFreeFieldBornSectionBij BookProof.ChapterFreeFieldGaussian BookProof.ChapterFreeFieldSphere BookProof.ChapterFreeFieldSphereSupport BookProof.ChapterFreeFieldBorn BookProof.ChapterFreeFieldBornSurj in
theorem solution {n : ℕ} {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ nonnegOrthant n) :
    bornSection (bornMap x) = x := by
  ext k
  simp only [bornSection, bornMap]
  exact Real.sqrt_sq (hx k)
