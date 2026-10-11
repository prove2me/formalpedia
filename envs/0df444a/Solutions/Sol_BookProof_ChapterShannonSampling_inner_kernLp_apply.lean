-- Prove2me | solution 1 for BookProof.ChapterShannonSampling.inner_kernLp_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:32:16.212371+00:00
-- url     : https://prove2.me/submissions/c84d14a8-3749-42f1-8fdf-435988ad5c0a

-- Generated from ChapterShannonSampling.lean — solution of BookProof.ChapterShannonSampling.inner_kernLp_apply
import Mathlib
import Definitions.Def_ChapterShannonSampling
open BookProof.ChapterShannonSampling




open MeasureTheory Complex AddCircle intervalIntegral Set
open scoped Real ComplexConjugate

variable {T : ℝ} [hT : Fact (0 < T)]

set_option maxHeartbeats 1000000 in
theorem solution (F : Lp ℂ 2 (haarAddCircle (T := T))) (x : ℝ) :
    inner ℂ (kernLp (T := T) x) F
      = ∫ z : AddCircle T, conj (kern (T := T) x z) * F z ∂haarAddCircle := by

  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_kern (T := T) x).coeFn_toLp] with z hz
  rw [RCLike.inner_apply, show ((kernLp (T := T) x : AddCircle T → ℂ) z) = kern (T := T) x z
    from hz]
  ring
