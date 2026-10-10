-- Prove2me | solution 1 for BookProof.LocalOperators.localIntegral_shift
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:39:30.633886+00:00
-- url     : https://prove2.me/submissions/d9076149-c999-4f17-80eb-499148d196c7

-- Generated from ChapterLocalOperators.lean — solution of BookProof.LocalOperators.localIntegral_shift
import Mathlib
import Definitions.Def_ChapterLocalOperators
import Theorems.Thm_BookProof_LocalOperators_localIntegral_translation_invariant
open BookProof.LocalOperators




open MeasureTheory

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution (l : LocalField d E) (y : Fin d → ℝ) :
    localIntegral (fun x => l (x + y)) = localIntegral l := localIntegral_translation_invariant l y
