-- Prove2me | solution 1 for BookProof.WeakSecondDeriv.eq_zero_out
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T17:20:56.746384+00:00
-- url     : https://prove2.me/submissions/96996b67-93d5-444e-a643-5cf122d26387

-- Generated from ChapterWeakSecondDerivative.lean — solution of BookProof.WeakSecondDeriv.eq_zero_out
import Mathlib
import Definitions.Def_ChapterWeakSecondDerivative
open BookProof.WeakSecondDeriv




open MeasureTheory Filter Topology intervalIntegral Set

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {g : ℝ → ℝ} {R : ℝ} (hsupp : tsupport g ⊆ Icc (-R) R)
    {x : ℝ} (hx : x ∉ Icc (-R) R) : g x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hsupp h))
