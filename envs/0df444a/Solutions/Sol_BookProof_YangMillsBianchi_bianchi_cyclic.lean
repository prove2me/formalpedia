-- Prove2me | solution 1 for BookProof.YangMillsBianchi.bianchi_cyclic
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-08T02:19:28.373755+00:00
-- url     : https://prove2.me/submissions/ef2ac24e-bc7f-43b8-b806-539d80d01a0d

-- Generated from ChapterYangMillsBianchi.lean — solution of BookProof.YangMillsBianchi.bianchi_cyclic
import Mathlib.Algebra.Jordan.Basic
import Mathlib
import Definitions.Def_ChapterYangMillsBianchi
open BookProof.YangMillsBianchi

attribute [local instance 100] LieRing.ofAssociativeRing










open BigOperators



variable {R : Type*} [Ring R]

set_option maxHeartbeats 1000000 in
theorem solution (D : Fin 3 → R) (i j k : Fin 3) :
    ⁅D i, ⁅D j, D k⁆⁆ + ⁅D j, ⁅D k, D i⁆⁆ + ⁅D k, ⁅D i, D j⁆⁆ = 0 := lie_jacobi (D i) (D j) (D k)
