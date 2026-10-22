-- Prove2me | solution 1 for BookProof.NavierStokesFlow.SignFlip.conj_esgn_inc
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-22T03:58:21.560136+00:00
-- url     : https://prove2.me/submissions/a0991abf-c9fd-41a3-9e72-1752d6c59006

import Mathlib
import Definitions.Def_ChapterNavierStokesSignFlip
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.SignFlip


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato HermiteFarisLavine ShiftHamiltonian AffineFiber

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
variable {ι : Type*}

theorem solution (c : ℝ) : (starRingEnd ℂ) (esgn c) = esgn c := by
  apply BookProof.NavierStokesFlow.SignFlip.conj_esgn <;> assumption

