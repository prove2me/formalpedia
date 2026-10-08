-- Prove2me | solution 1 for BookProof.ChapterFreeFieldBornCont.continuous_bornMap
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T03:42:22.576969+00:00
-- url     : https://prove2.me/submissions/0ea8be8b-24ad-4e4f-8c69-5b435b0fddff

import Mathlib
import Definitions.Def_ChapterFreeFieldBorn
import Definitions.Def_ChapterFreeFieldBornSurj
import Definitions.Def_ChapterFreeFieldBornCont

set_option autoImplicit false

open MeasureTheory BookProof.ChapterFreeFieldBornCont BookProof.ChapterFreeFieldBorn BookProof.ChapterFreeFieldBornSurj in
theorem solution {n : ℕ} :
    Continuous (bornMap : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ)) := by
  apply continuous_pi
  intro k
  show Continuous (fun x : EuclideanSpace ℝ (Fin n) => (x k) ^ 2)
  fun_prop
