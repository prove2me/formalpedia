-- Prove2me | solution 1 for BookProof.NavierStokesFlow.SignedShift.SignedHop.maj_amp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T10:30:50.734891+00:00
-- url     : https://prove2.me/submissions/fef072fc-8363-4451-a725-7f956a81a465

-- Generated from ChapterNavierStokesSignedShift.lean — solution of BookProof.NavierStokesFlow.SignedShift.SignedHop.maj_amp
import Mathlib
import Definitions.Def_ChapterNavierStokesSignedShift
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.SignedShift
open BookProof.NavierStokesFlow.SignedShift.SignedHop










open scoped ENNReal



open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ShiftHamiltonian BookProof.NavierStokesFlow.AffineFiber

variable {ι : Type*}



variable {sym : ι → ℝ} (S : SignedHop ι sym)

set_option maxHeartbeats 1000000 in
theorem solution : S.maj.amp = S.bnd := rfl
