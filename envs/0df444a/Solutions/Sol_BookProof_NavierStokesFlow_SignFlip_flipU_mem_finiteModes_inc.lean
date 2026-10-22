-- Prove2me | solution 1 for BookProof.NavierStokesFlow.SignFlip.flipU_mem_finiteModes_inc
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-22T03:58:23.184986+00:00
-- url     : https://prove2.me/submissions/4f9c943a-3102-4311-9866-ea933652c339

import Mathlib
import Definitions.Def_ChapterNavierStokesSignFlip
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.SignFlip


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato HermiteFarisLavine ShiftHamiltonian AffineFiber

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
variable {ι : Type*}

theorem solution (p : ι → ℕ) {x : L2I ι} (hx : x ∈ lpFiniteModes ι) :
    flipU p x ∈ lpFiniteModes ι := by
  apply BookProof.NavierStokesFlow.SignFlip.flipU_mem_finiteModes <;> assumption

