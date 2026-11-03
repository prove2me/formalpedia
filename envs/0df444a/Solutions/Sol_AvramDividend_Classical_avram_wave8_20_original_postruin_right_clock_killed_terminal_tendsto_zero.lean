-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_20_original_postruin_right_clock_killed_terminal_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T23:41:19.99724+00:00
-- url     : https://prove2.me/submissions/05fd5ef0-d7f6-497d-b81b-1032e9d5c133

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_strict_survival_terminal_zero_at_after_ruin
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
open AvramDividend.Classical

/-- The original strictly killed terminal is identically zero on post-ruin clocks. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (q : ℝ)
    (ω : Ω) (t : ℝ≥0)
    (hRuin : ruinTime X x D ω ≤ (t : ℝ≥0∞))
    (τ : ℕ → ℝ≥0) (hRight : ∀ n, t ≤ τ n) :
    Filter.Tendsto
      (fun n : ℕ =>
        if (τ n : ℝ≥0∞) < ruinTime X x D ω then
          max 0 (Real.exp (-(q * (τ n : ℝ))) *
            w (x + X.X (τ n) ω - rightLimit D (τ n) ω))
        else 0) Filter.atTop (𝓝 (0 : ℝ)) := by
  have hZero (n : ℕ) :
      (if (τ n : ℝ≥0∞) < ruinTime X x D ω then
        max 0 (Real.exp (-(q * (τ n : ℝ))) *
          w (x + X.X (τ n) ω - rightLimit D (τ n) ω))
      else 0) = 0 :=
    avram_wave8_20_original_strict_survival_terminal_zero_at_after_ruin
      X x D w q ω t hRuin (τ n) (hRight n)
  have hEq :
      (fun n : ℕ =>
        if (τ n : ℝ≥0∞) < ruinTime X x D ω then
          max 0 (Real.exp (-(q * (τ n : ℝ))) *
            w (x + X.X (τ n) ω - rightLimit D (τ n) ω))
        else 0) = (fun _ : ℕ => (0 : ℝ)) :=
    funext hZero
  rw [hEq]
  exact tendsto_const_nhds
