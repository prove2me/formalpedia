-- Prove2me | solution 1 for BookProof.ChapterPinOmega.Omega_mul_closed
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T10:00:21.099824+00:00
-- url     : https://prove2.me/submissions/833d7e55-acfa-4225-84cb-365731237104

-- Generated from ChapterPinOmega.lean — solution of BookProof.ChapterPinOmega.Omega_mul_closed
import Mathlib
import Definitions.Def_ChapterPinOmega
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterPinDoubleCover
open BookProof.ChapterPinOmega



open Matrix


open BookProof.ChapterA3

set_option maxHeartbeats 1000000 in
theorem solution : ∀ x ∈ Omega, ∀ y ∈ Omega, x * y ∈ Omega := by
 decide
