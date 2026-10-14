-- Prove2me | solution 1 for BookProof.ChapterWignerOrbitClassification.eq_zero_of_energy_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:53:54.784984+00:00
-- url     : https://prove2.me/submissions/5a5aafc5-2b43-4d04-a2a3-591de831674d

-- Generated from ChapterWignerOrbitClassification.lean — solution of BookProof.ChapterWignerOrbitClassification.eq_zero_of_energy_zero
import Mathlib
import Definitions.Def_ChapterWignerOrbitClassification
import Definitions.Def_ChapterWignerLittleGroup
import Definitions.Def_ChapterWignerLittleGroupOrbits
import Definitions.Def_ChapterGravityProjector
open BookProof.ChapterWignerOrbitClassification



open Matrix Complex


open BookProof.ChapterWignerLittleGroup BookProof.ChapterWignerLittleGroupOrbits

set_option maxHeartbeats 1000000 in
theorem solution {p : Fin 4 → ℝ} (hmass : 0 ≤ minkSq p) (h0 : p 0 = 0) :
    ∀ i, p i = 0 := by

  have hle : p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2 ≤ 0 := by
    simp only [minkSq, h0] at hmass
    nlinarith [hmass]
  have h1 : p 1 = 0 := by nlinarith [sq_nonneg (p 1), sq_nonneg (p 2), sq_nonneg (p 3)]
  have h2 : p 2 = 0 := by nlinarith [sq_nonneg (p 1), sq_nonneg (p 2), sq_nonneg (p 3)]
  have h3 : p 3 = 0 := by nlinarith [sq_nonneg (p 1), sq_nonneg (p 2), sq_nonneg (p 3)]
  intro i
  fin_cases i
  · simpa using h0
  · simpa using h1
  · simpa using h2
  · simpa using h3
