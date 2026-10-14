-- Prove2me | solution 1 for BookProof.ChapterWignerOrbitClassification.hermOfMom_negMom
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:53:25.804484+00:00
-- url     : https://prove2.me/submissions/0d7ae4be-d1cb-4776-8acc-58f7564ccc12

-- Generated from ChapterWignerOrbitClassification.lean — solution of BookProof.ChapterWignerOrbitClassification.hermOfMom_negMom
import Mathlib
import Definitions.Def_ChapterWignerOrbitClassification
import Definitions.Def_ChapterWignerLittleGroupOrbits
import Definitions.Def_ChapterWignerLittleGroup
open BookProof.ChapterWignerOrbitClassification



open Matrix Complex


open BookProof.ChapterWignerLittleGroup BookProof.ChapterWignerLittleGroupOrbits

set_option maxHeartbeats 1000000 in
theorem solution (p : Fin 4 → ℝ) : hermOfMom (negMom p) = -hermOfMom p := by

  ext i j
  fin_cases i <;> fin_cases j <;> simp [hermOfMom, negMom] <;> ring
