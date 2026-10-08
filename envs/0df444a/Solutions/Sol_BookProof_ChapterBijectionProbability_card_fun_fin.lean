-- Prove2me | solution 1 for BookProof.ChapterBijectionProbability.card_fun_fin
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T23:34:27.07999+00:00
-- url     : https://prove2.me/submissions/c09ad6fd-295a-4a53-94be-daf2c586d345

import Mathlib
import Definitions.Def_ChapterBijectionProbability

set_option autoImplicit false
set_option linter.all false

open BookProof BookProof.ChapterBijectionProbability in open BookProof.ChapterBijectionProbability in open scoped Nat in open Filter Asymptotics in
theorem solution (n : ℕ) : Fintype.card (Fin n → Fin n) = n ^ n := by
  intros
  norm_num
