-- Prove2me | solution 1 for BookProof.ChapterParity.higgsParity_pow_four
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T09:12:34.392181+00:00
-- url     : https://prove2.me/submissions/371d5391-289b-4420-8398-66ab15db433d

-- Generated from ChapterParity.lean — solution of BookProof.ChapterParity.higgsParity_pow_four
import Mathlib
import Definitions.Def_ChapterParity
import Theorems.Thm_BookProof_ChapterParity_higgsParity_sq
open BookProof.ChapterParity



open Matrix
open scoped ComplexConjugate

variable {n : Type*}

set_option maxHeartbeats 1000000 in
theorem solution :
    higgsParity * higgsParity * (higgsParity * higgsParity) = 1 := by

  rw [higgsParity_sq]; simp
