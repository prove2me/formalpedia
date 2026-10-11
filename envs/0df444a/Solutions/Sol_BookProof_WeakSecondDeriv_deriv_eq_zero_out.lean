-- Prove2me | solution 1 for BookProof.WeakSecondDeriv.deriv_eq_zero_out
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T17:20:57.950983+00:00
-- url     : https://prove2.me/submissions/a67a8e0f-5bfd-4a85-9e07-fe3b078b222e

-- Generated from ChapterWeakSecondDerivative.lean — solution of BookProof.WeakSecondDeriv.deriv_eq_zero_out
import Mathlib
import Definitions.Def_ChapterWeakSecondDerivative
open BookProof.WeakSecondDeriv




open MeasureTheory Filter Topology intervalIntegral Set

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {g : ℝ → ℝ} {R : ℝ} (hsupp : tsupport g ⊆ Icc (-R) R)
    {x : ℝ} (hx : x ∉ Icc (-R) R) : deriv g x = 0 := by

  by_contra hne
  exact hx (hsupp (support_deriv_subset (by exact hne)))
