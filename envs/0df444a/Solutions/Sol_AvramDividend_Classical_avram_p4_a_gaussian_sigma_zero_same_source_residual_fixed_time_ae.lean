-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_a_gaussian_sigma_zero_same_source_residual_fixed_time_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T07:49:37.70837+00:00
-- url     : https://prove2.me/submissions/fd02a51d-f5d8-410c-8e0d-d89ce620fb30

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_sigma_zero_drift_only_ae

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Under a literal same-path Gaussian/jump extraction, zero source Gaussian
coefficient kills the extracted residual at every fixed time, almost surely. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X Y : SpectrallyNegativeLevy P 𝓕)
    (hYν : Y.ν = 0) (hYσ : Y.σ = X.σ)
    (Jsmall Jlarge : ℝ≥0 → Ω → ℝ)
    (hSourceDecomp : ∀ (u : ℝ≥0) (ω : Ω),
      X.X u ω = (u : ℝ) * X.c +
        (Y.X u ω - (u : ℝ) * Y.c) + Jsmall u ω + Jlarge u ω)
    (hσ : X.σ = 0) (t : ℝ≥0) :
    ∀ᵐ ω ∂P,
      X.X t ω - (t : ℝ) * X.c - Jsmall t ω - Jlarge t ω = 0 := by
  have hYzero : Y.σ = 0 := hYσ.trans hσ
  have hStop : ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | (0 : ℝ≥0) ≤ s} := by
    intro s
    simp
  have hDrift := avram_wave6_03_original_rightCont_stopped_sigma_zero_drift_only_ae
    Y hYν hYzero (fun _ : Ω => (0 : ℝ≥0))
    hStop 0 (by intro ω; simp) t
  filter_upwards [hDrift] with ω h
  have hYt : Y.X t ω = (t : ℝ) * Y.c := by
    simpa [Y.X_zero ω] using h
  calc
    X.X t ω - (t : ℝ) * X.c - Jsmall t ω - Jlarge t ω =
        Y.X t ω - (t : ℝ) * Y.c := by rw [hSourceDecomp t ω]; ring
    _ = 0 := sub_eq_zero.mpr hYt
