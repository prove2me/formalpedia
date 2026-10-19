-- Prove2me | solution 1 for BookProof.ChapterFreeFieldBornFiberTwo.one_le_posSupport_card
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-16T23:57:57.096143+00:00
-- url     : https://prove2.me/submissions/0105dfc6-4443-41dd-91f4-394caf1b5392

-- Generated from ChapterFreeFieldBornFiberTwo.lean — solution of BookProof.ChapterFreeFieldBornFiberTwo.one_le_posSupport_card
import Mathlib
import Definitions.Def_ChapterFreeFieldBornFiberTwo
import Theorems.Thm_BookProof_ChapterFreeFieldBornFiberTwo_posSupport_nonempty
import Definitions.Def_ChapterFreeFieldBorn
import Definitions.Def_ChapterFreeFieldBornSurj
import Definitions.Def_ChapterFreeFieldBornCont
import Definitions.Def_ChapterFreeFieldBornQuotient
import Definitions.Def_ChapterFreeFieldBornFiberCardGeneral
open BookProof.ChapterFreeFieldBornFiberTwo



open MeasureTheory
open BookProof.ChapterFreeFieldBorn BookProof.ChapterFreeFieldBornSurj
open BookProof.ChapterFreeFieldBornCont BookProof.ChapterFreeFieldBornQuotient
open BookProof.ChapterFreeFieldBornFiberCardGeneral


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {p : Fin n → ℝ} (hp : p ∈ stdSimplex ℝ (Fin n)) :
    1 ≤ (posSupport p).card := (posSupport_nonempty hp).card_pos
