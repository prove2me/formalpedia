-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_20_original_all_right_clocks_killed_terminal_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T10:00:03.762674+00:00
-- url     : https://prove2.me/submissions/7fdb8c86-380f-4279-ad25-85f8ef6922ab

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
    (τ : ℕ → ℝ≥0)
    (hτ : Filter.Tendsto τ Filter.atTop (𝓝 t))
    (hRight : ∀ n, t ≤ τ n) :
    Filter.Tendsto
      (fun n : ℕ =>
        if (τ n : ℝ≥0∞) < ruinTime X x D ω then
          max 0 (Real.exp (-(q * (τ n : ℝ))) *
            w (x + X.X (τ n) ω - rightLimit D (τ n) ω))
        else 0) Filter.atTop
      (𝓝 (if (t : ℝ≥0∞) < ruinTime X x D ω then
        max 0 (Real.exp (-(q * (t : ℝ))) *
          w (x + X.X t ω - rightLimit D t ω))
        else 0)) := by
  by_cases hp : (t : ℝ≥0∞) < ruinTime X x D ω
  · let S : Set ℝ≥0 := {s | t ≤ s ∧ (s : ℝ≥0∞) < ruinTime X x D ω}
    have hOpen : IsOpen {s : ℝ≥0 |
        (s : ℝ≥0∞) < ruinTime X x D ω} :=
      avram_wave8_20_original_strict_preruin_time_set_open X x D ω
    have hevent : ∀ᶠ n : ℕ in atTop,
        (τ n : ℝ≥0∞) < ruinTime X x D ω :=
      hτ.eventually (hOpen.mem_nhds hp)
    have hmem : ∀ᶠ n : ℕ in atTop, τ n ∈ S := by
      filter_upwards [hevent] with n hn
      exact ⟨hRight n, hn⟩
    have hwithin : Tendsto τ atTop (𝓝[S] t) :=
      tendsto_nhdsWithin_iff.mpr ⟨hτ, hmem⟩
    have hc : ContinuousWithinAt
        (fun s : ℝ≥0 => max 0 (Real.exp (-(q * (s : ℝ))) *
          w (x + X.X s ω - rightLimit D s ω))) S t :=
      avram_wave8_20_original_preruin_discounted_positive_postpayment_terminal_rightContinuous
        X x D hD w hw_cont q ω t hp
    have hlimit := hc.tendsto.comp hwithin
    simp only [if_pos hp]
    refine hlimit.congr' ?_
    filter_upwards [hevent] with n hn
    simp [hn]
  · have hnone : ∀ n : ℕ,
        ¬ (τ n : ℝ≥0∞) < ruinTime X x D ω := by
      intro n hn
      have hle : (t : ℝ≥0∞) ≤ (τ n : ℝ≥0∞) := by
        exact_mod_cast hRight n
      exact hp (lt_of_le_of_lt hle hn)
    simpa [hp, hnone] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ))
        atTop (𝓝 (0 : ℝ)))
