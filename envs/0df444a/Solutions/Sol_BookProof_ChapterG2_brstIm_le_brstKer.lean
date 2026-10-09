-- Prove2me | solution 1 for BookProof.ChapterG2.brstIm_le_brstKer
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:21:43.207981+00:00
-- url     : https://prove2.me/submissions/6fa7e500-4666-4ca8-90db-90eb854c4b82

-- Generated from ChapterG2.lean — solution of BookProof.ChapterG2.brstIm_le_brstKer
import Mathlib
import Definitions.Def_ChapterG2
open BookProof.ChapterG
open BookProof.ChapterG2



open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]
variable {A : Type*} [CommRing A] (Q : A)

set_option maxHeartbeats 1000000 in
theorem solution : brstIm Q ≤ brstKer Q := by

  intro v hv; simp_all [ brstIm, brstKer,BRST ] ;
  rcases hv with ⟨ y, rfl ⟩ ; simp [ Matrix.vecHead ]
