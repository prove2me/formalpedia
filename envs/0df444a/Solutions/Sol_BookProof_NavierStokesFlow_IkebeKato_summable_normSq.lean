-- Prove2me | solution 1 for BookProof.NavierStokesFlow.IkebeKato.summable_normSq
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T04:45:48.971142+00:00
-- url     : https://prove2.me/submissions/28332491-1de0-4f63-9c54-fbda1c47722a

import Mathlib
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa

set_option autoImplicit false

universe u

open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato in
theorem solution {ι : Type u} (f : L2I ι) : Summable fun k => ‖(f : ι → ℂ) k‖ ^ 2 := by
  have h := (lp.memℓp f).summable (by norm_num : 0 < (2 : ENNReal).toReal)
  simpa [Real.rpow_two] using h
