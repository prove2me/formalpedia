-- Prove2me | solution 1 for BookProof.ChapterFreeFieldBornFiberBounds.bornFiber_card_eq_iff_posSupport_card_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T01:06:33.821643+00:00
-- url     : https://prove2.me/submissions/7432c74f-2715-423a-b37d-d2b49843b561

-- Generated from ChapterFreeFieldBornFiberBounds.lean — solution of BookProof.ChapterFreeFieldBornFiberBounds.bornFiber_card_eq_iff_posSupport_card_eq
import Mathlib
import Definitions.Def_ChapterFreeFieldBornFiberBounds
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
theorem solution
    {p q : ↥(stdSimplex ℝ (Fin n))} :
    Nat.card ↥(bornMapSphere n ⁻¹' {p}) = Nat.card ↥(bornMapSphere n ⁻¹' {q}) ↔
      (posSupport (p : Fin n → ℝ)).card = (posSupport (q : Fin n → ℝ)).card := by

  rw [bornFiber_card_general, bornFiber_card_general]
  exact (Nat.pow_right_injective (le_refl 2)).eq_iff
