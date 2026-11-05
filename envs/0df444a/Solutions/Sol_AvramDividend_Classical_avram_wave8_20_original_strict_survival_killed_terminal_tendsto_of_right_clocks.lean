-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_20_original_strict_survival_killed_terminal_tendsto_of_right_clocks
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T10:01:41.349248+00:00
-- url     : https://prove2.me/submissions/ed752343-6627-479a-bb9f-858d93f08be1

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_strict_preruin_time_set_open
import Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_preruin_discounted_positive_postpayment_terminal_rightContinuous

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (q : ℝ) (ω : Ω) (t : ℝ≥0)
    (ht : (t : ℝ≥0∞) < ruinTime X x D ω)
    (τ : ℕ → ℝ≥0)
    (hτ : Filter.Tendsto τ Filter.atTop (𝓝 t))
    (hτRight : ∀ n, t ≤ τ n) :
    Filter.Tendsto
      (fun n : ℕ =>
        if (τ n : ℝ≥0∞) < ruinTime X x D ω then
          max 0 (Real.exp (-(q * (τ n : ℝ))) *
            w (x + X.X (τ n) ω - rightLimit D (τ n) ω))
        else 0) Filter.atTop
      (𝓝 (max 0 (Real.exp (-(q * (t : ℝ))) *
        w (x + X.X t ω - rightLimit D t ω)))) := by
  let S : Set ℝ≥0 := {s | t ≤ s ∧ (s : ℝ≥0∞) < ruinTime X x D ω}
  have hOpen : IsOpen {s : ℝ≥0 |
      (s : ℝ≥0∞) < ruinTime X x D ω} :=
    avram_wave8_20_original_strict_preruin_time_set_open X x D ω
  have hevent : ∀ᶠ n : ℕ in atTop,
      (τ n : ℝ≥0∞) < ruinTime X x D ω :=
    hτ.eventually (hOpen.mem_nhds ht)
  have hmem : ∀ᶠ n : ℕ in atTop, τ n ∈ S := by
    filter_upwards [hevent] with n hn
    exact ⟨hτRight n, hn⟩
  have hwithin : Tendsto τ atTop (𝓝[S] t) :=
    tendsto_nhdsWithin_iff.mpr ⟨hτ, hmem⟩
  have hc : ContinuousWithinAt
      (fun s : ℝ≥0 => max 0 (Real.exp (-(q * (s : ℝ))) *
        w (x + X.X s ω - rightLimit D s ω))) S t :=
    avram_wave8_20_original_preruin_discounted_positive_postpayment_terminal_rightContinuous
      X x D hD w hw_cont q ω t ht
  have hlimit := hc.tendsto.comp hwithin
  refine hlimit.congr' ?_
  filter_upwards [hevent] with n hn
  simp [hn]
