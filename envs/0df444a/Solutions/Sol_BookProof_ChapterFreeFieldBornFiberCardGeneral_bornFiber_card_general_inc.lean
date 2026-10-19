-- Prove2me | solution 1 for BookProof.ChapterFreeFieldBornFiberCardGeneral.bornFiber_card_general_inc
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T20:38:48.163622+00:00
-- url     : https://prove2.me/submissions/15b58e69-816d-403d-abad-4a3476c7b1cb

-- Generated from ChapterFreeFieldBornFiberCardGeneral.lean — solution of BookProof.ChapterFreeFieldBornFiberCardGeneral.bornFiber_card_general_inc
import Mathlib
import Definitions.Def_ChapterFreeFieldBornFiberCardGeneral
import Definitions.Def_ChapterFreeFieldBorn
import Definitions.Def_ChapterFreeFieldBornSurj
import Definitions.Def_ChapterFreeFieldBornCont
import Definitions.Def_ChapterFreeFieldBornSignGauge
import Definitions.Def_ChapterFreeFieldBornSignFiber
import Definitions.Def_ChapterFreeFieldBornSectionBij
import Definitions.Def_ChapterFreeFieldBornQuotient
import Definitions.Def_ChapterFreeFieldBornFiberCard
open BookProof.ChapterFreeFieldBornFiberCardGeneral



open MeasureTheory
open BookProof.ChapterFreeFieldBorn BookProof.ChapterFreeFieldBornSurj
open BookProof.ChapterFreeFieldBornCont BookProof.ChapterFreeFieldBornSignGauge
open BookProof.ChapterFreeFieldBornSignFiber BookProof.ChapterFreeFieldBornSectionBij
open BookProof.ChapterFreeFieldBornQuotient BookProof.ChapterFreeFieldBornFiberCard


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {p : ↥(stdSimplex ℝ (Fin n))} :
    Nat.card ↥(bornMapSphere n ⁻¹' {p}) = 2 ^ (posSupport (p : Fin n → ℝ)).card := by

  convert Nat.card_congr ( bornFiberEquivGeneral.symm ) using 1
  rw [ Nat.card_eq_fintype_card, Fintype.card_pi ]
  norm_num
