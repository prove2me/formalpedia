-- Prove2me | solution 1 for BookProof.NavierStokesFlow.SignFlip.sblockH_essentiallySelfAdjointOn_core_inc
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-21T08:21:26.683992+00:00
-- url     : https://prove2.me/submissions/f241a62f-fbb7-462d-bd03-cbcad850c9c9

-- Generated from ChapterNavierStokesSignFlip.lean — solution of BookProof.NavierStokesFlow.SignFlip.sblockH_essentiallySelfAdjointOn_core_inc
import Mathlib
import Definitions.Def_ChapterNavierStokesSignFlip
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesIkebeKato
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.SignFlip



open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato HermiteFarisLavine ShiftHamiltonian AffineFiber
open BookProof.NavierStokesFlow.AffineFiber.PairShift

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
variable {ι : Type*}
variable {J : Type*}

set_option maxHeartbeats 1000000 in
theorem solution (κ c : J → ℝ) (hκ : ∀ j, 0 ≤ κ j) :
    EssentiallySelfAdjointOn (lpFiniteModes (ℕ × J)) (sblockH κ c hκ) :=
  ⟨deficiencyTrivialAt_sblockH κ c hκ Complex.I
        fun j => (saffH_essentiallySelfAdjointOn_core (hκ j) (c j)).1,
     deficiencyTrivialAt_sblockH κ c hκ (-Complex.I)
        fun j => (saffH_essentiallySelfAdjointOn_core (hκ j) (c j)).2⟩
