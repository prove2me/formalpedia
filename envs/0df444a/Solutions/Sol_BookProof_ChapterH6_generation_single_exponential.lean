-- Prove2me | solution 1 for BookProof.ChapterH6.generation_single_exponential
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T00:52:04.542908+00:00
-- url     : https://prove2.me/submissions/c5527b0c-8167-422c-8dc9-f8816d032cb0

import Mathlib
import Definitions.Def_ChapterH6

set_option autoImplicit false

open BookProof.ChapterH6 in
theorem solution {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) (psi0 : Fin m → ℂ) :
    generatedState A 1 psi0 = (NormedSpace.exp ((-Complex.I) • A)).mulVec psi0 := by
  unfold generatedState
  rw [mul_one]
