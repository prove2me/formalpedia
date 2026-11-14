-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb78_original_true_T_survivor_discounted_terminal_uniform_grid_left_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:35:50.089842+00:00
-- url     : https://prove2.me/submissions/9b35e414-4c81-48d8-bafa-6015f5d36e06

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_excess30_original_discounted_prepayment_surviving_horizon_left_limit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (x : ℝ) (w : ℝ → ℝ) (hw : ContinuousOn w (Ici 0)) (q : ℝ)
    (t : ℝ≥0) (ht : 0 < t)
    (u : ℕ → ℝ≥0) (hu : Tendsto u atTop (𝓝[<] t)) :
    ∀ᵐ ω ∂P, (t : ℝ≥0∞) < ruinTime X x D ω →
      Tendsto (fun n =>
        if (u n : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * ((u n) : ℝ))) * w (riskProcess X x D (u n) ω) else 0)
        atTop
        (𝓝 (Real.exp (-(q * (t : ℝ))) * w (riskProcess X x D t ω))) := by
  classical
  filter_upwards
    [avram_bv_excess30_original_discounted_prepayment_surviving_horizon_left_limit
      X D hD x w hw q t ht] with ω hω
  intro hsurv
  have huLt : ∀ᶠ n : ℕ in atTop, u n < t := by
    exact hu.eventually self_mem_nhdsWithin
  have hBefore : ∀ᶠ n : ℕ in atTop,
      (u n : ℝ≥0∞) < ruinTime X x D ω := by
    filter_upwards [huLt] with n hn
    have hnTop : (u n : ℝ≥0∞) < (t : ℝ≥0∞) := by
      exact_mod_cast hn
    exact hnTop.trans hsurv
  have hRaw :
      Tendsto
        (fun n => Real.exp (-(q * ((u n) : ℝ))) * w (riskProcess X x D (u n) ω))
        atTop
        (𝓝 (Real.exp (-(q * (t : ℝ))) * w (riskProcess X x D t ω))) :=
    (hω hsurv).comp hu
  have hSame : (fun n : ℕ =>
        if (u n : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * ((u n) : ℝ))) * w (riskProcess X x D (u n) ω)
        else 0) =ᶠ[atTop]
      (fun n => Real.exp (-(q * ((u n) : ℝ))) *
        w (riskProcess X x D (u n) ω)) := by
    filter_upwards [hBefore] with n hn
    simp [hn]
  exact hRaw.congr' hSame.symm
