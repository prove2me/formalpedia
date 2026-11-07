-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_error7_compact_continuous_deriv_uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T09:41:20.36819+00:00
-- url     : https://prove2.me/submissions/28d59714-23eb-427e-a10d-2be198386e5e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Continuity of the genuine C1 derivative on a compact source band
provides a global nonnegative bound for the original Taylor errors. -/
theorem solution
    (w : ℝ → ℝ) (a b : ℝ)
    (hDerCont : ContinuousOn (deriv w) (Set.Icc a b)) :
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ y ∈ Set.Icc a b, |deriv w y| ≤ L := by
  obtain ⟨L, hBound⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc a b)).exists_bound_of_continuousOn
      hDerCont
  refine ⟨max L 0, le_max_right _ _, ?_⟩
  intro y hy
  have h := (hBound y hy).trans (le_max_left L 0)
  simpa only [Real.norm_eq_abs] using h
