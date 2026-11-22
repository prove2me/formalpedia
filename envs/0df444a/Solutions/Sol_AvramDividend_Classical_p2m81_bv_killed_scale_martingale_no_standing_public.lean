-- Prove2me | solution 1 for AvramDividend.Classical.p2m81_bv_killed_scale_martingale_no_standing_public
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T07:09:19.966306+00:00
-- url     : https://prove2.me/submissions/cd300107-1ebc-4353-889a-bd2a64b4f6f2

import Mathlib
import Theorems.Thm_AvramDividend_Classical_chat04_explicit_shifted_killed_survival_schedule
import Theorems.Thm_AvramDividend_Classical_chat03_killed_scale_payoff_adapted
import Theorems.Thm_AvramDividend_Classical_p2m81_bv_future_window_killed_scale_integrable_no_standing
import Theorems.Thm_AvramDividend_Classical_chat04_killed_discounted_condExp_time_split
import Theorems.Thm_AvramDividend_Classical_p2m81_bv_future_window_killed_scale_harmonicity_no_standing_public

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

/-- Standing-free BV killed q-scale martingale from a positive Esscher root. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (x : ℝ) :
    Martingale (fun t ω =>
      ({ω | ∀ v : ℝ≥0, v ≤ t → 0 ≤ x + X.X v ω}).indicator
        (fun ω => Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω)) ω) 𝓕 P := by
  obtain ⟨τ, hCover, _⟩ :=
    chat04_explicit_shifted_killed_survival_schedule (1 : ℝ≥0)
  have hAdapted : Adapted 𝓕 (fun t ω =>
      ({ω | ∀ v : ℝ≥0, v ≤ t → 0 ≤ x + X.X v ω}).indicator
        (fun ω => Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω)) ω) :=
    chat03_killed_scale_payoff_adapted X τ hCover q x W hW
  refine ⟨hAdapted.stronglyAdapted, ?_⟩
  intro s u hsu
  have hInt : Integrable
      (({ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
        0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)}).indicator
        (fun ω => Real.exp (-(q * ((u : ℝ) - (s : ℝ)))) *
          W (x + X.X u ω))) P :=
    p2m81_bv_future_window_killed_scale_integrable_no_standing
      X q φ hq hφ hroot W hW x s u hsu
  have hSplit :=
    chat04_killed_discounted_condExp_time_split
      X τ hCover q W x s u hsu hInt
  have hFuture :=
    p2m81_bv_future_window_killed_scale_harmonicity_no_standing_public
      X q φ hq hφ hroot W hW hBV x s u hsu
  filter_upwards [hSplit, hFuture] with ω hsω hfω
  calc
    P[({ω | ∀ v : ℝ≥0, v ≤ u → 0 ≤ x + X.X v ω}).indicator
      (fun ω => Real.exp (-(q * (u : ℝ))) * W (x + X.X u ω)) | 𝓕 s] ω = ({ω | ∀ v : ℝ≥0, v ≤ s → 0 ≤ x + X.X v ω}).indicator
      (fun ω => Real.exp (-(q * (s : ℝ))) * P[({ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
        0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)}).indicator
      (fun ω => Real.exp (-(q * ((u : ℝ) - (s : ℝ)))) *
        W (x + X.X u ω)) | 𝓕 s] ω) ω := hsω
    _ = ({ω | ∀ v : ℝ≥0, v ≤ s → 0 ≤ x + X.X v ω}).indicator
      (fun ω => Real.exp (-(q * (s : ℝ))) * W (x + X.X s ω)) ω := by
      by_cases h : ω ∈ ({ω | ∀ v : ℝ≥0, v ≤ s → 0 ≤ x + X.X v ω})
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, hfω]
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]
