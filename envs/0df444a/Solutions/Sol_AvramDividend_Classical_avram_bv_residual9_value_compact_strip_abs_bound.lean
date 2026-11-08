-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual9_value_compact_strip_abs_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T13:40:21.470447+00:00
-- url     : https://prove2.me/submissions/9239ef11-7782-42c1-b4dc-2e1b80a665c4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original value candidate has a deterministic bound on each finite nonnegative drift strip. -/
theorem solution
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (H : ℝ) (hH : 0 ≤ H) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ z : ℝ, 0 ≤ z → z ≤ H → |w z| ≤ K := by
  have hsub : Icc (0 : ℝ) H ⊆ Ici (0 : ℝ) := by
    intro z hz
    exact hz.1
  have hcont : ContinuousOn w (Icc (0 : ℝ) H) :=
    hw_cont.mono hsub
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨max K 0, le_max_right _ _, ?_⟩
  intro z hz hZH
  have hb : ‖w z‖ ≤ K := hK z ⟨hz, hZH⟩
  have habs : |w z| ≤ K := by simpa only [Real.norm_eq_abs] using hb
  exact habs.trans (le_max_left _ _)
