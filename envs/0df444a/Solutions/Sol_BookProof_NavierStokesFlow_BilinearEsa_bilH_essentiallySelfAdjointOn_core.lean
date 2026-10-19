-- Prove2me | solution 1 for BookProof.NavierStokesFlow.BilinearEsa.bilH_essentiallySelfAdjointOn_core
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T01:23:56.698958+00:00
-- url     : https://prove2.me/submissions/04bad56b-1a73-4cc7-94b8-790e8c6d500d

-- Generated from ChapterNavierStokesBilinearEsa.lean — solution of BookProof.NavierStokesFlow.BilinearEsa.bilH_essentiallySelfAdjointOn_core
import Mathlib
import Definitions.Def_ChapterNavierStokesBilinearEsa
import Theorems.Thm_BookProof_NavierStokesFlow_BilinearEsa_deficiencyTrivialAt_bilH
import Theorems.Thm_BookProof_NavierStokesFlow_HermiteFarisLavine_nsH_essentiallySelfAdjointOn_core
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.BilinearEsa



open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato HermiteFarisLavine

variable {J : Type*}

variable {J : Type*}

set_option maxHeartbeats 1000000 in
theorem solution (κ : J → ℝ) (hκ : ∀ j, 0 ≤ κ j) :
    EssentiallySelfAdjointOn (lpFiniteModes (ℕ × J)) (bilH κ) :=
  ⟨deficiencyTrivialAt_bilH κ hκ Complex.I
        fun j => (nsH_essentiallySelfAdjointOn_core (hκ j)).1,
     deficiencyTrivialAt_bilH κ hκ (-Complex.I)
        fun j => (nsH_essentiallySelfAdjointOn_core (hκ j)).2⟩
