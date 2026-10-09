-- Prove2me | solution 1 for BookProof.ChapterFiniteArithmeticPrior.certainExtension_known
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:11:25.68678+00:00
-- url     : https://prove2.me/submissions/7daebfc6-296c-4db5-af2a-da6042c82284

-- Generated from ChapterFiniteArithmeticPrior.lean — solution of BookProof.ChapterFiniteArithmeticPrior.certainExtension_known
import Mathlib
import Definitions.Def_ChapterFiniteArithmeticPrior
open BookProof.ChapterFiniteArithmeticPrior

set_option maxHeartbeats 1000000 in
theorem solution {B : ℕ} (A : BoundedArithmetic B) :
    (certainExtension A).known = A := by

  rfl
