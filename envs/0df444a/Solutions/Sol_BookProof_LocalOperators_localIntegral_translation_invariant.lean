-- Prove2me | solution 1 for BookProof.LocalOperators.localIntegral_translation_invariant
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:39:18.990171+00:00
-- url     : https://prove2.me/submissions/61d25764-e7cf-41a7-84a3-f91856701ce7

-- Generated from ChapterLocalOperators.lean — solution of BookProof.LocalOperators.localIntegral_translation_invariant
import Mathlib
import Definitions.Def_ChapterLocalOperators
open BookProof.LocalOperators




open MeasureTheory

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution (l : LocalField d E) (y : Fin d → ℝ) :
    (∫ x, l (x + y)) = ∫ x, l x := integral_add_right_eq_self l y
