-- Prove2me | solution 1 for BookProof.HalfLineLimitCircle.setIntegral_eq_integral_of_testSpace
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:38:11.998462+00:00
-- url     : https://prove2.me/submissions/cd6d9be6-080c-43b2-9e32-855034167d78

-- Generated from ChapterHalfLineLimitCircle.lean — solution of BookProof.HalfLineLimitCircle.setIntegral_eq_integral_of_testSpace
import Mathlib
import Definitions.Def_ChapterHalfLineLimitCircle
import Definitions.Def_ChapterFarisLavine
open BookProof.HalfLineLimitCircle




open MeasureTheory Set BookProof.FarisLavine

noncomputable section

local notation "smoothTop" => ((⊤ : ℕ∞) : WithTop ℕ∞)

set_option maxHeartbeats 1000000 in
theorem solution {f : ℝ → ℂ} (hf : f ∈ testSpace) (w : ℝ → ℂ) :
    ∫ x in Ioi (0 : ℝ), (starRingEnd ℂ) (f x) * w x = ∫ x, (starRingEnd ℂ) (f x) * w x := by

  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
  rw [eq_zero_of_notMem_Ioi hf hx]
  simp
