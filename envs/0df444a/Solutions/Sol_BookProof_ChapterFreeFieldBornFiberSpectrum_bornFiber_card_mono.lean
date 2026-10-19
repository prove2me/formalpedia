-- Prove2me | solution 1 for BookProof.ChapterFreeFieldBornFiberSpectrum.bornFiber_card_mono
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T01:06:38.714226+00:00
-- url     : https://prove2.me/submissions/c3c39917-c637-4262-85f2-fdb490a06e94

-- Generated from ChapterFreeFieldBornFiberSpectrum.lean — solution of BookProof.ChapterFreeFieldBornFiberSpectrum.bornFiber_card_mono
import Mathlib
import Definitions.Def_ChapterFreeFieldBornFiberSpectrum
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
theorem solution {p q : ↥(stdSimplex ℝ (Fin n))}
    (h : posSupport (p : Fin n → ℝ) ⊆ posSupport (q : Fin n → ℝ)) :
    Nat.card ↥(bornMapSphere n ⁻¹' {p}) ≤ Nat.card ↥(bornMapSphere n ⁻¹' {q}) := by

  convert Nat.pow_le_pow_right ( by norm_num : 1 ≤ 2 ) ( Finset.card_le_card h ) using 1;
  · convert bornFiber_card_general using 1;
  · convert BookProof.ChapterFreeFieldBornFiberCardGeneral.bornFiber_card_general
