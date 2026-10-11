-- Prove2me | solution 1 for BookProof.ChapterParityZ4.combinedParity_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T00:12:22.711696+00:00
-- url     : https://prove2.me/submissions/00c3762b-23e5-4bf8-9845-81ac5bed1008

-- Generated from ChapterParityZ4.lean — solution of BookProof.ChapterParityZ4.combinedParity_sq
import Mathlib
import Definitions.Def_ChapterParityZ4
import Theorems.Thm_BookProof_ChapterParityQL_QLParity_sq
import Theorems.Thm_BookProof_ChapterParity_higgsParity_sq
import Theorems.Thm_BookProof_ChapterParity_mgamma0_sq
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterParity
import Definitions.Def_ChapterParityQL
open BookProof.ChapterParityZ4



open Matrix


open BookProof.ChapterParity
open BookProof.ChapterParityQL
open BookProof.ChapterA3

set_option maxHeartbeats 1000000 in
theorem solution :
    combinedParity ^ 2 = (-1, -1, -1, -1) := by

  simp only [combinedParity, Fin.isValue, Prod.pow_mk, Prod.mk.injEq, and_self];
  exact ⟨ by simpa [ sq ] using higgsParity_sq, by simpa [ sq ] using QLParity_sq,
                                                   by simpa [ sq ] using mgamma0_sq ⟩
