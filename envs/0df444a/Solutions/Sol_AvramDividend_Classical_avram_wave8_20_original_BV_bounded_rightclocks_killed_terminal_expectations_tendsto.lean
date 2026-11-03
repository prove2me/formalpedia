-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_20_original_BV_bounded_rightclocks_killed_terminal_expectations_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T00:22:01.704661+00:00
-- url     : https://prove2.me/submissions/1dc4f2ee-e39d-414b-b71e-05e71e1f5eb7

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_preruin_discounted_postpayment_positivepart_right_clock_limit
import Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_postruin_right_clock_killed_terminal_tendsto_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_eventually_strict_survival_of_clock_tendsto
import Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_BV_bounded_measurable_clocks_terminal_DCT
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
open AvramDividend.Classical

/-- Source killed terminal DCT along bounded right-clocks, including ruin. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (H : ℝ≥0) (t : Ω → ℝ≥0) (τ : ℕ → Ω → ℝ≥0)
    (hτMeas : ∀ n, Measurable (τ n))
    (hτBound : ∀ n ω, τ n ω ≤ H)
    (hRight : ∀ n ω, t ω ≤ τ n ω)
    (hRightTend : ∀ᵐ ω ∂P, Tendsto (fun n => τ n ω) atTop (𝓝 (t ω))) :
    Tendsto (fun n : ℕ => ∫ ω, (if (τ n ω : ℝ≥0∞) < ruinTime X x D ω then
          max 0 (Real.exp (-(q * (τ n ω : ℝ))) *
            w (x + X.X (τ n ω) ω - rightLimit D (τ n ω) ω))
        else 0) ∂P) atTop
      (𝓝 (∫ ω, (if (t ω : ℝ≥0∞) < ruinTime X x D ω then
          max 0 (Real.exp (-(q * (t ω : ℝ))) *
            w (x + X.X (t ω) ω - rightLimit D (t ω) ω))
        else 0) ∂P)) := by
  have hStrat : IsDividendStrategy 𝓕 D := hD.1.1
  have hConv : ∀ᵐ ω ∂P, Tendsto
      (fun n : ℕ => (if (τ n ω : ℝ≥0∞) < ruinTime X x D ω then
          max 0 (Real.exp (-(q * (τ n ω : ℝ))) *
            w (x + X.X (τ n ω) ω - rightLimit D (τ n ω) ω))
        else 0)) atTop
      (𝓝 (if (t ω : ℝ≥0∞) < ruinTime X x D ω then
          max 0 (Real.exp (-(q * (t ω : ℝ))) *
            w (x + X.X (t ω) ω - rightLimit D (t ω) ω))
        else 0)) := by
    filter_upwards [hRightTend] with ω hω
    by_cases hs : (t ω : ℝ≥0∞) < ruinTime X x D ω
    · have hRaw :=
        avram_wave8_20_original_preruin_discounted_postpayment_positivepart_right_clock_limit
          X x D hStrat w hw_cont q ω (t ω) hs
            (fun n => τ n ω) hω (fun n => hRight n ω)
      have hEventually :=
        avram_wave8_20_original_eventually_strict_survival_of_clock_tendsto
          X x D ω (t ω) hs (fun n => τ n ω) hω
      have hEq : (fun n : ℕ => (if (τ n ω : ℝ≥0∞) < ruinTime X x D ω then
          max 0 (Real.exp (-(q * (τ n ω : ℝ))) *
            w (x + X.X (τ n ω) ω - rightLimit D (τ n ω) ω))
        else 0)) =ᶠ[atTop]
          (fun n => max 0 (Real.exp (-(q * (τ n ω : ℝ))) *
            w (x + X.X (τ n ω) ω - rightLimit D (τ n ω) ω))) := by
        filter_upwards [hEventually] with n hn
        simp only [if_pos hn]
      simpa only [if_pos hs] using hRaw.congr' hEq.symm
    · have hRuin : ruinTime X x D ω ≤ (t ω : ℝ≥0∞) :=
        le_of_not_gt hs
      have hZero :=
        avram_wave8_20_original_postruin_right_clock_killed_terminal_tendsto_zero
          X x D w q ω (t ω) hRuin (fun n => τ n ω)
          (fun n => hRight n ω)
      simpa only [if_neg hs] using hZero
  exact avram_wave8_20_original_BV_bounded_measurable_clocks_terminal_DCT
    X hX hBV q hq w hw_cont hw_neg x C D hD H τ
      hτMeas hτBound (fun ω => (if (t ω : ℝ≥0∞) < ruinTime X x D ω then
          max 0 (Real.exp (-(q * (t ω : ℝ))) *
            w (x + X.X (t ω) ω - rightLimit D (t ω) ω))
        else 0)) hConv
