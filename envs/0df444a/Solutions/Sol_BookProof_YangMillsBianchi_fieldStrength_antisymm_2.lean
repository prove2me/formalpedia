-- Prove2me | solution 2 for BookProof.YangMillsBianchi.fieldStrength_antisymm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-08T05:54:48.883987+00:00
-- url     : https://prove2.me/submissions/8d2457bb-8edf-4990-8a65-3d20554277a5

-- Generated from ChapterYangMillsBianchi.lean — solution of BookProof.YangMillsBianchi.fieldStrength_antisymm
import Mathlib
import Mathlib.Algebra.Jordan.Basic
import Definitions.Def_ChapterYangMillsBianchi
open BookProof.YangMillsBianchi

open BigOperators

attribute [local instance 100] LieRing.ofAssociativeRing










open BigOperators



variable {R : Type*} [Ring R]

set_option maxHeartbeats 1000000 in
theorem solution (D : Fin 3 → R) (j k : Fin 3) :
    fieldStrength D j k = - fieldStrength D k j := by

  simp only [fieldStrength]
  exact (lie_skew (D j) (D k)).symm
