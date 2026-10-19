-- Prove2me | solution 1 for BookProof.ChapterFreeFieldBornFiberSpectrum.bornFiber_card_achievable_iff
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-16T23:58:02.212+00:00
-- url     : https://prove2.me/submissions/2f58bba5-7edc-4ca7-af06-8d05d5a523f8

-- Generated from ChapterFreeFieldBornFiberSpectrum.lean — solution of BookProof.ChapterFreeFieldBornFiberSpectrum.bornFiber_card_achievable_iff
import Mathlib
import Definitions.Def_ChapterFreeFieldBornFiberSpectrum
import Theorems.Thm_BookProof_ChapterFreeFieldBornFiberSpectrum_bornFiber_card_isPowerOfTwo
import Theorems.Thm_BookProof_ChapterFreeFieldBornFiberSpectrum_exists_bornFiber_card_eq_two_pow
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
theorem solution {c : ℕ} :
    (∃ p : ↥(stdSimplex ℝ (Fin n)), Nat.card ↥(bornMapSphere n ⁻¹' {p}) = c) ↔
      ∃ k, 1 ≤ k ∧ k ≤ n ∧ c = 2 ^ k := by

  constructor
  · rintro ⟨p, rfl⟩
    obtain ⟨k, hk₁, hk₂, hk⟩ := bornFiber_card_isPowerOfTwo (p := p)
    exact ⟨k, hk₁, hk₂, hk⟩
  · rintro ⟨k, hk₁, hk₂, rfl⟩
    exact exists_bornFiber_card_eq_two_pow hk₁ hk₂
