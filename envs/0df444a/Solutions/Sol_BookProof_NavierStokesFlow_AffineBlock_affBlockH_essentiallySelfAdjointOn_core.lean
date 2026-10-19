-- Prove2me | solution 1 for BookProof.NavierStokesFlow.AffineBlock.affBlockH_essentiallySelfAdjointOn_core
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T01:23:44.593078+00:00
-- url     : https://prove2.me/submissions/79d0f275-9b5a-43c5-99d0-13b1be8e4c25

-- Generated from ChapterNavierStokesAffineBlockEsa.lean — solution of BookProof.NavierStokesFlow.AffineBlock.affBlockH_essentiallySelfAdjointOn_core
import Mathlib
import Definitions.Def_ChapterNavierStokesAffineBlockEsa
import Theorems.Thm_BookProof_NavierStokesFlow_AffineBlock_deficiencyTrivialAt_affBlockH
import Theorems.Thm_BookProof_NavierStokesFlow_AffineFiber_affH_essentiallySelfAdjointOn_core
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesIkebeKato
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.AffineBlock



open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato HermiteFarisLavine ShiftHamiltonian AffineFiber BilinearEsa
open BookProof.NavierStokesFlow.AffineFiber.PairShift

variable {J : Type*}

variable {J : Type*}

set_option maxHeartbeats 1000000 in
theorem solution (κ c : J → ℝ) (hκ : ∀ j, 0 ≤ κ j)
    (hc : ∀ j, 0 ≤ c j) :
    EssentiallySelfAdjointOn (lpFiniteModes (ℕ × J)) (affBlockH κ c hκ hc) :=
  ⟨deficiencyTrivialAt_affBlockH κ c hκ hc Complex.I
        fun j => (affH_essentiallySelfAdjointOn_core (hκ j) (hc j)).1,
     deficiencyTrivialAt_affBlockH κ c hκ hc (-Complex.I)
        fun j => (affH_essentiallySelfAdjointOn_core (hκ j) (hc j)).2⟩
