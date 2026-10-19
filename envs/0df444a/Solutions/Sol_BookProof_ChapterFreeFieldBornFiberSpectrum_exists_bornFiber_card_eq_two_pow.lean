-- Prove2me | solution 1 for BookProof.ChapterFreeFieldBornFiberSpectrum.exists_bornFiber_card_eq_two_pow
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T01:06:39.893252+00:00
-- url     : https://prove2.me/submissions/e217b39e-4c24-435c-97ba-77b64de8a6f4

-- Generated from ChapterFreeFieldBornFiberSpectrum.lean — solution of BookProof.ChapterFreeFieldBornFiberSpectrum.exists_bornFiber_card_eq_two_pow
import Mathlib
import Definitions.Def_ChapterFreeFieldBornFiberSpectrum
import Theorems.Thm_BookProof_ChapterFreeFieldBornFiberSpectrum_unifDist_mem_simplex
import Theorems.Thm_BookProof_ChapterFreeFieldBornFiberSpectrum_posSupport_unifDist_card
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
theorem solution {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    ∃ p : ↥(stdSimplex ℝ (Fin n)),
      Nat.card ↥(bornMapSphere n ⁻¹' {p}) = 2 ^ k := by

  use ⟨unifDist n k, unifDist_mem_simplex hk hkn⟩;
  convert bornFiber_card_general;
  exact Eq.symm ( posSupport_unifDist_card hk hkn )
