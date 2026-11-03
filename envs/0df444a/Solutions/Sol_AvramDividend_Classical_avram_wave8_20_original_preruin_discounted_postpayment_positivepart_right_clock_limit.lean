-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_20_original_preruin_discounted_postpayment_positivepart_right_clock_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T00:09:56.71617+00:00
-- url     : https://prove2.me/submissions/10754143-d8f9-414c-b760-ab2c53dd7efc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_preruin_HJB_postpayment_rightContinuous
import Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_eventually_strict_survival_of_clock_tendsto
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
open AvramDividend.Classical

/-- Strictly before ruin the original discounted postpayment positive part has a right-clock limit. -/
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
      (fun n : ℕ => max 0 (Real.exp (-(q * (τ n : ℝ))) *
        w (x + X.X (τ n) ω - rightLimit D (τ n) ω)))
      Filter.atTop
      (𝓝 (max 0 (Real.exp (-(q * (t : ℝ))) *
        w (x + X.X t ω - rightLimit D t ω)))) := by
  let S : Set ℝ≥0 :=
    {s | t ≤ s ∧ (s : ℝ≥0∞) < ruinTime X x D ω}
  have hW : ContinuousWithinAt
      (fun s : ℝ≥0 => w (x + X.X s ω - rightLimit D s ω)) S t :=
    avram_wave8_20_original_preruin_HJB_postpayment_rightContinuous
      X x D hD w hw_cont ω t ht
  have hExp : Continuous (fun s : ℝ≥0 => Real.exp (-(q * (s : ℝ)))) :=
    Real.continuous_exp.comp
      ((continuous_const.mul NNReal.continuous_coe).neg)
  have hRaw : ContinuousWithinAt
      (fun s : ℝ≥0 => Real.exp (-(q * (s : ℝ))) *
        w (x + X.X s ω - rightLimit D s ω)) S t :=
    hExp.continuousWithinAt.mul hW
  have hMax : Continuous (fun y : ℝ => max (0 : ℝ) y) :=
    continuous_const.max continuous_id
  have hPos : ContinuousWithinAt
      (fun s : ℝ≥0 => max 0 (Real.exp (-(q * (s : ℝ))) *
        w (x + X.X s ω - rightLimit D s ω))) S t := by
    change ContinuousWithinAt
      ((fun y : ℝ => max (0 : ℝ) y) ∘
        (fun s : ℝ≥0 => Real.exp (-(q * (s : ℝ))) *
          w (x + X.X s ω - rightLimit D s ω))) S t
    exact hMax.continuousAt.comp_continuousWithinAt hRaw
  have hSurvive :=
    avram_wave8_20_original_eventually_strict_survival_of_clock_tendsto
      X x D ω t ht τ hτ
  have hInS : ∀ᶠ n in Filter.atTop, τ n ∈ S := by
    filter_upwards [hSurvive] with n hn
    exact ⟨hτRight n, hn⟩
  have hWithin : Filter.Tendsto τ Filter.atTop (𝓝[S] t) :=
    tendsto_nhdsWithin_iff.mpr ⟨hτ, hInS⟩
  have hPosTend : Filter.Tendsto
      (fun n : ℕ => max 0 (Real.exp (-(q * (τ n : ℝ))) *
        w (x + X.X (τ n) ω - rightLimit D (τ n) ω)))
      Filter.atTop
      (𝓝 (max 0 (Real.exp (-(q * (t : ℝ))) *
        w (x + X.X t ω - rightLimit D t ω)))) :=
    hPos.tendsto.comp hWithin
  exact hPosTend
