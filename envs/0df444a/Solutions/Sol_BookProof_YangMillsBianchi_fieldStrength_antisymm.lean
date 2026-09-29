-- Prove2me | solution 1 for BookProof.YangMillsBianchi.fieldStrength_antisymm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-08T05:54:32.669793+00:00
-- url     : https://prove2.me/submissions/74a43256-f985-42e2-9e02-908c28b3dafe

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
