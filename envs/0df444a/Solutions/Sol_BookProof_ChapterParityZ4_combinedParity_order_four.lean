-- Prove2me | solution 1 for BookProof.ChapterParityZ4.combinedParity_order_four
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T00:12:24.795421+00:00
-- url     : https://prove2.me/submissions/26f34dc3-e15d-4712-910c-67407619d65e

-- Generated from ChapterParityZ4.lean — solution of BookProof.ChapterParityZ4.combinedParity_order_four
import Mathlib
import Definitions.Def_ChapterParityZ4
import Theorems.Thm_BookProof_ChapterParityZ4_combinedParity_sq_ne_one
import Theorems.Thm_BookProof_ChapterParityZ4_combinedParity_pow_four
import Definitions.Def_ChapterParity
import Definitions.Def_ChapterParityQL
import Definitions.Def_ChapterA3
open BookProof.ChapterParityZ4



open Matrix


open BookProof.ChapterParity
open BookProof.ChapterParityQL
open BookProof.ChapterA3

set_option maxHeartbeats 1000000 in
theorem solution :
    combinedParity ^ 2 ≠ 1 ∧ combinedParity ^ 4 = 1 := ⟨combinedParity_sq_ne_one, combinedParity_pow_four⟩
