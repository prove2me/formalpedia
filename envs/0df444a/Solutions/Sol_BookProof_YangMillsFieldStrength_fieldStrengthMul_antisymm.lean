-- Prove2me | solution 1 for BookProof.YangMillsFieldStrength.fieldStrengthMul_antisymm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-07T16:26:06.380535+00:00
-- url     : https://prove2.me/submissions/03e0568b-8406-4e37-8433-e3860f5eb31f

-- Generated from ChapterYangMillsFieldStrength.lean — solution of BookProof.YangMillsFieldStrength.fieldStrengthMul_antisymm
import Mathlib
import Definitions.Def_ChapterYangMillsFieldStrength
open BookProof.YangMillsFieldStrength














open Complex



variable {R : Type*} [Ring R]

set_option maxHeartbeats 1000000 in
theorem solution (δ : Fin 3 → R → R) (a : Fin 3 → R) (j k : Fin 3) :
    fieldStrengthMul δ a j k = - fieldStrengthMul δ a k j := by

  simp only [fieldStrengthMul]; noncomm_ring
