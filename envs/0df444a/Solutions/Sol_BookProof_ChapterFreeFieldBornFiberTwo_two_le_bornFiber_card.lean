-- Prove2me | solution 1 for BookProof.ChapterFreeFieldBornFiberTwo.two_le_bornFiber_card
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T01:06:31.323526+00:00
-- url     : https://prove2.me/submissions/f7066c3d-2d76-4dcb-a565-ff05c4b44e51

-- Generated from ChapterFreeFieldBornFiberTwo.lean — solution of BookProof.ChapterFreeFieldBornFiberTwo.two_le_bornFiber_card
import Mathlib
import Definitions.Def_ChapterFreeFieldBornFiberTwo
import Theorems.Thm_BookProof_ChapterFreeFieldBornFiberTwo_one_le_posSupport_card
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
theorem solution {p : ↥(stdSimplex ℝ (Fin n))} :
    2 ≤ Nat.card ↥(bornMapSphere n ⁻¹' {p}) := by

  convert Nat.pow_le_pow_right ( by decide : 1 ≤ 2 ) ( one_le_posSupport_card p.2 ) using 1;
  convert bornFiber_card_general
  rfl
