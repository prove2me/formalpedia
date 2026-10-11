-- Prove2me | solution 1 for BookProof.ChapterSuperBracket.sbracket_graded_antisymm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T16:10:27.430163+00:00
-- url     : https://prove2.me/submissions/74e8c9fb-0737-492e-917c-fb28d7f64b67

-- Generated from ChapterSuperBracket.lean — solution of BookProof.ChapterSuperBracket.sbracket_graded_antisymm
import Mathlib
import Definitions.Def_ChapterSuperBracket
import Definitions.Def_ChapterElectroweakFieldStrength
open BookProof.ChapterSuperBracket




variable {R : Type*} [Ring R]

variable {R : Type*} [Ring R]

set_option maxHeartbeats 1000000 in
theorem solution (p q : Bool) (a b : R) :
    sbracket p q a b = - (eps p q : R) * sbracket q p b a := by

  cases p <;> cases q <;>
    · simp only [sbracket, eps, Bool.and_true, Bool.and_false]
      push_cast
      noncomm_ring
