-- Prove2me | solution 1 for BookProof.FreeEMField.emFieldStrength_antisymm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:16:35.770501+00:00
-- url     : https://prove2.me/submissions/1f3e78e4-d910-451c-af87-55d5a036c0b6

-- Generated from ChapterFreeEMField.lean — solution of BookProof.FreeEMField.emFieldStrength_antisymm
import Mathlib
import Definitions.Def_ChapterFreeEMField
open BookProof.FreeEMField




open BookProof.YangMillsFieldStrength


variable {R : Type*} [Ring R]

variable {R : Type*} [Ring R]

set_option maxHeartbeats 1000000 in
theorem solution (δ : Fin 3 → R → R) (A : Fin 3 → R) (j k : Fin 3) :
    emFieldStrength δ A j k = - emFieldStrength δ A k j := by

  simp only [emFieldStrength]; abel
