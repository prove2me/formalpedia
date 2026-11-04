-- Prove2me | solution 2 for AvramDividend.Classical.avram_p4_a_gaussian_ubv_C2_moving_band_taylor_lagrange
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:28:37.070582+00:00
-- url     : https://prove2.me/submissions/cf0661e1-6a9c-416f-aae9-35de62b3b73a

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The first-order Taylor remainder at two arbitrary reserve levels
inside a compact strict source band has its exact Lagrange form. -/
theorem solution
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hwC2 : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hBand : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (u v : ℝ) (hu : u ∈ Icc a b) (hv : v ∈ Icc a b)
    (huv : u ≠ v) :
    ∃ ξ ∈ uIoo u v,
      w v - taylorWithinEval w 1 (uIcc u v) u v =
        iteratedDeriv 2 w ξ * (v - u) ^ 2 / 2 := by
  have hSegment : uIcc u v ⊆ Icc a b :=
    Set.uIcc_subset_Icc hu hv
  have hwSegment : ContDiffOn ℝ (1 + 1) w (uIcc u v) := by
    simpa only [one_add_one_eq_two] using
      (hwC2.mono (hSegment.trans hBand))
  obtain ⟨ξ, hξ, hTaylor⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv
      (n := 1) huv hwSegment
  refine ⟨ξ, hξ, ?_⟩
  norm_num at hTaylor ⊢
  exact hTaylor
