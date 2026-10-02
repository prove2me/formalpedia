-- Prove2me | solution 1 for BookProof.ChapterH6.generation_semigroup
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T02:48:43.347002+00:00
-- url     : https://prove2.me/submissions/284bc333-159a-4e86-ad30-9171301f37af

import Mathlib
import Definitions.Def_ChapterH6

set_option autoImplicit false

open BookProof.ChapterH6 in
theorem solution {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) (s t : ℂ)
    (psi0 : Fin m → ℂ) :
    generatedState A (s + t) psi0 = generatedState A s (generatedState A t psi0) := by
  unfold generatedState
  rw [Matrix.mulVec_mulVec, ← Matrix.exp_add_of_commute]
  · congr 2
    rw [mul_add, add_smul]
  · exact ((Commute.refl A).smul_left _).smul_right _
