-- Prove2me | solution 2 for BookProof.YangMillsBianchi.bianchi_fieldStrength
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-08T02:28:29.292607+00:00
-- url     : https://prove2.me/submissions/93b9cc3c-9e7f-451d-9c8a-fbd4b8eeca1e

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
