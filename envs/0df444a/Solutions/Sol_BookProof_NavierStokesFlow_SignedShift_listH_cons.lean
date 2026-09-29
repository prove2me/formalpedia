-- Prove2me | solution 1 for BookProof.NavierStokesFlow.SignedShift.listH_cons
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T10:39:55.686194+00:00
-- url     : https://prove2.me/submissions/e0155ae7-989e-47d6-9c96-bcc616807dc7

-- Generated from ChapterNavierStokesSignedShift.lean — solution of BookProof.NavierStokesFlow.SignedShift.listH_cons
import Mathlib
import Definitions.Def_ChapterNavierStokesSignedShift
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.SignedShift










open scoped ENNReal



open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ShiftHamiltonian BookProof.NavierStokesFlow.AffineFiber

variable {ι : Type*}



variable {sym : ι → ℝ} (S : SignedHop ι sym)


































variable {sym : ι → ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (S : SignedHop ι sym) (L : List (SignedHop ι sym)) :
    listH (S :: L) = SignedHop.hopH S + listH L := rfl
