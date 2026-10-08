-- Prove2me | solution 1 for BookProof.ChapterFreeFieldBornCont.continuous_bornSection
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T01:05:30.043025+00:00
-- url     : https://prove2.me/submissions/d8e51e74-8cea-49da-af69-a4f34058f818

import Mathlib
import Definitions.Def_ChapterFreeFieldBorn
import Definitions.Def_ChapterFreeFieldBornSurj
import Definitions.Def_ChapterFreeFieldBornCont

open MeasureTheory BookProof.ChapterFreeFieldBornCont BookProof.ChapterFreeFieldBorn BookProof.ChapterFreeFieldBornSurj in
theorem solution {n : ℕ} :
    Continuous (bornSection : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) := by
  unfold bornSection
  exact (PiLp.continuous_toLp 2 _).comp
    (continuous_pi fun k => Real.continuous_sqrt.comp (continuous_apply k))
