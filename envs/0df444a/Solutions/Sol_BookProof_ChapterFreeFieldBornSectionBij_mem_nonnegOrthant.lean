-- Prove2me | solution 1 for BookProof.ChapterFreeFieldBornSectionBij.mem_nonnegOrthant
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T20:22:11.296863+00:00
-- url     : https://prove2.me/submissions/9c798f2b-68d8-47ad-af56-2e6730a174df

import Mathlib
import Definitions.Def_ChapterFreeFieldGaussian
import Definitions.Def_ChapterFreeFieldSphere
import Definitions.Def_ChapterFreeFieldSphereSupport
import Definitions.Def_ChapterFreeFieldBorn
import Definitions.Def_ChapterFreeFieldBornSurj
import Definitions.Def_ChapterFreeFieldBornSectionBij

open MeasureTheory
open BookProof.ChapterFreeFieldGaussian BookProof.ChapterFreeFieldSphere
open BookProof.ChapterFreeFieldSphereSupport BookProof.ChapterFreeFieldBorn
open BookProof.ChapterFreeFieldBornSurj
open BookProof.ChapterFreeFieldBornSectionBij

open BookProof.ChapterFreeFieldBornSectionBij in
theorem solution {n : ℕ} {x : EuclideanSpace ℝ (Fin n)} :
    x ∈ nonnegOrthant n ↔ ∀ k, 0 ≤ x k := by
  exact Iff.rfl

