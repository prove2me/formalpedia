-- Prove2me | solution 1 for BookProof.YangMillsBianchi.bianchi_fieldStrength
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-08T02:27:22.15602+00:00
-- url     : https://prove2.me/submissions/fc18368f-65c1-4c59-9ee4-43314bc5028c

-- Generated from ChapterYangMillsBianchi.lean — solution of BookProof.YangMillsBianchi.bianchi_fieldStrength
import Mathlib
import Definitions.Def_ChapterYangMillsBianchi
import Theorems.Thm_BookProof_YangMillsBianchi_bianchi
open BookProof.YangMillsBianchi










open BigOperators



variable {R : Type*} [Ring R]

set_option maxHeartbeats 1000000 in
theorem solution (D : Fin 3 → R) :
    ∑ i, ∑ j, ∑ k, (eps i j k) • ⁅D i, fieldStrength D j k⁆ = 0 := by

  simpa only [fieldStrength] using bianchi D
