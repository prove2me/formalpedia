-- Prove2me | solution 1 for BookProof.ChapterFreeFieldBornFiberSpectrum.bornFiber_card_even
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T01:06:34.963218+00:00
-- url     : https://prove2.me/submissions/d76a3828-3321-457f-ba38-d13bfa95d58f

-- Generated from ChapterFreeFieldBornFiberSpectrum.lean — solution of BookProof.ChapterFreeFieldBornFiberSpectrum.bornFiber_card_even
import Mathlib
import Definitions.Def_ChapterFreeFieldBornFiberSpectrum
import Theorems.Thm_BookProof_ChapterFreeFieldBornFiberTwo_one_le_posSupport_card
import Definitions.Def_ChapterFreeFieldBorn
import Definitions.Def_ChapterFreeFieldBornSurj
import Definitions.Def_ChapterFreeFieldBornCont
import Definitions.Def_ChapterFreeFieldBornQuotient
import Definitions.Def_ChapterFreeFieldBornFiberCardGeneral
import Definitions.Def_ChapterFreeFieldBornFiberTwo
import Definitions.Def_ChapterFreeFieldBornFiberBounds
open BookProof.ChapterFreeFieldBornFiberSpectrum



open MeasureTheory
open BookProof.ChapterFreeFieldBorn BookProof.ChapterFreeFieldBornSurj
open BookProof.ChapterFreeFieldBornCont BookProof.ChapterFreeFieldBornQuotient
open BookProof.ChapterFreeFieldBornFiberCardGeneral
open BookProof.ChapterFreeFieldBornFiberTwo
open BookProof.ChapterFreeFieldBornFiberBounds


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {p : ↥(stdSimplex ℝ (Fin n))} :
    2 ∣ Nat.card ↥(bornMapSphere n ⁻¹' {p}) := by

  rw [ bornFiber_card_general ];
  exact dvd_pow_self _ ( Nat.ne_of_gt ( one_le_posSupport_card p.2 ) )
