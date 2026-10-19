-- Prove2me | solution 1 for BookProof.ChapterFreeFieldBornFiberBounds.bornFiber_card_le_two_pow_n
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T01:06:32.661286+00:00
-- url     : https://prove2.me/submissions/b12e0aa5-4d2a-427c-a919-4d0098216980

-- Generated from ChapterFreeFieldBornFiberBounds.lean — solution of BookProof.ChapterFreeFieldBornFiberBounds.bornFiber_card_le_two_pow_n
import Mathlib
import Definitions.Def_ChapterFreeFieldBornFiberBounds
import Theorems.Thm_BookProof_ChapterFreeFieldBornFiberBounds_posSupport_card_le_n
import Definitions.Def_ChapterFreeFieldBorn
import Definitions.Def_ChapterFreeFieldBornSurj
import Definitions.Def_ChapterFreeFieldBornCont
import Definitions.Def_ChapterFreeFieldBornQuotient
import Definitions.Def_ChapterFreeFieldBornFiberCardGeneral
import Definitions.Def_ChapterFreeFieldBornFiberTwo
open BookProof.ChapterFreeFieldBornFiberBounds



open MeasureTheory
open BookProof.ChapterFreeFieldBorn BookProof.ChapterFreeFieldBornSurj
open BookProof.ChapterFreeFieldBornCont BookProof.ChapterFreeFieldBornQuotient
open BookProof.ChapterFreeFieldBornFiberCardGeneral
open BookProof.ChapterFreeFieldBornFiberTwo


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {p : ↥(stdSimplex ℝ (Fin n))} :
    Nat.card ↥(bornMapSphere n ⁻¹' {p}) ≤ 2 ^ n := by

  rw [bornFiber_card_general]
  exact Nat.pow_le_pow_right (by decide) posSupport_card_le_n
