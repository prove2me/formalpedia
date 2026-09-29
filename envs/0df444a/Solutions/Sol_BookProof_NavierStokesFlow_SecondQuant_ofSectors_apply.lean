-- Prove2me | solution 1 for BookProof.NavierStokesFlow.SecondQuant.ofSectors_apply
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-10T21:51:28.751476+00:00
-- url     : https://prove2.me/submissions/a33b8d42-eac0-42ac-beda-f88b55b316b9

import Mathlib
import Definitions.Def_ChapterNavierStokesSecondQuant
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.SecondQuant
open scoped ENNReal

variable {ι : Type*}
variable {S : ι → Type*} [∀ m, NormedAddCommGroup (S m)] [∀ m, InnerProductSpace ℂ (S m)]

theorem solution (g : ∀ m, S m) (h : (Function.support fun m => ‖g m‖).Finite)
    (m : ι) : (ofSectors g h : ∀ m, S m) m = g m := by
  rfl
