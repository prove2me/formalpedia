-- Prove2me | solution 1 for AvramDividend.Classical.esscher_bounded_stop_stoppedHistory_density_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T18:39:29.077016+00:00
-- url     : https://prove2.me/submissions/cd778e79-9af1-4cde-91f3-6fa6e23984df

import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_bounded_stop_explicit_grid_increment_limit_with_horizon
import Theorems.Thm_AvramDividend_Classical_stoppedHistory_event_measurable
import Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_stoppedEvent_density_eq_of_upper_grids

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Topology
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ : ℝ) (hθ : 0 ≤ θ)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (H : ℝ≥0) (hbound : ∀ ω, τ ω ≤ H)
    (T : ℝ≥0) (hT : H + 1 ≤ T)
    (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s})) :
    (P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))) A =
    (P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X (τ ω) ω -
        (τ ω : ℝ) * X.ψ θ)))) A := by
  classical
  let τn : ℕ → Ω → ℝ≥0 := fun n ω =>
    (Nat.ceil ((τ ω : ℝ) * (2 : ℝ) ^ n) : ℝ≥0) /
      (2 : ℝ≥0) ^ n
  let grid : ℕ → Finset ℝ≥0 := fun n =>
    (Finset.range (Nat.ceil ((H : ℝ) * (2 : ℝ) ^ n) + 1)).image
      (fun k : ℕ => (k : ℝ≥0) / (2 : ℝ≥0) ^ n)
  obtain ⟨hmem, hfib, hgridBound, habove, hlim, _⟩ :=
    bounded_stop_explicit_grid_increment_limit_with_horizon
      X τ hstop H hbound (0 : ℝ≥0)
  have hMeasA : MeasurableSet A :=
    stoppedHistory_event_measurable τ A hA
  have hTgrid : ∀ n s, s ∈ grid n → s ≤ T := by
    intro n s hs
    exact (hgridBound n s hs).trans hT
  have hupperBound : ∀ n ω, τn n ω ≤ H + 1 := by
    intro n ω
    exact hgridBound n (τn n ω) (hmem n ω)
  exact esscher_bounded_stop_stoppedEvent_density_eq_of_upper_grids
    X θ hθ T (H + 1) τ τn grid
    hmem hTgrid hfib hupperBound hlim habove
    A hMeasA hA

