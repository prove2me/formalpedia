-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03_actual_discounted_finite_band_inclusive_ruin_chronological_jump_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T10:10:37.740188+00:00
-- url     : https://prove2.me/submissions/3dd860c9-30d6-4709-b437-e1d5212dae48

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_canonical_hjump_inclusive_ruin_source_discounted_jump_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (q : ℝ)
    (u v ζ : ℝ) (s t : ℝ≥0) (ω : Ω)
    (B : Set ℝ) (hBneg : B ⊆ Iio (0 : ℝ))
    (S : Finset ℝ≥0)
    (hS : ∀ r : ℝ≥0, r ∈ S ↔
      s < r ∧ r ≤ t ∧
        X.X r ω - Function.leftLim (fun a : ℝ≥0 => X.X a ω) r ∈ B) :
    let Y : ℝ≥0 → ℝ := fun r => Function.leftLim
      (fun a : ℝ≥0 => x + X.X a ω - rightLimit D a ω) r
    let J : ℝ≥0 → ℝ := fun r =>
      X.X r ω - Function.leftLim (fun a : ℝ≥0 => X.X a ω) r
    let W : ℝ≥0 → ℝ := fun r =>
      if (r : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X r ω - rightLimit D r ω
      else riskProcess X x D r ω
    let cash : ℝ≥0 → ℝ := fun r =>
      if (r : ℝ≥0∞) < ruinTime X x D ω then
        rightLimit D r ω - D r ω else 0
    (∑ r ∈ S, if (r : ℝ≥0∞) ≤ ruinTime X x D ω then
      (if Y r ∈ Icc (u + ζ) v then
        Real.exp (-(q * (r : ℝ))) *
        ((w (W r) - w (Function.leftLim
          (fun a : ℝ≥0 => riskProcess X x D a ω) r)) + cash r)
       else 0) else 0) ≤
    (∑ r ∈ S, if (r : ℝ≥0∞) ≤ ruinTime X x D ω then
      (if Y r ∈ Icc (u + ζ) v then
        Real.exp (-(q * (r : ℝ))) *
          ((if -1 < J r then J r * deriv w (Y r) else 0) +
           SpectrallyNegativeLevy.generatorIntegrand w (Y r) (J r))
       else 0) else 0) := by
  dsimp only
  let Y : ℝ≥0 → ℝ := fun r => Function.leftLim
    (fun a : ℝ≥0 => x + X.X a ω - rightLimit D a ω) r
  let J : ℝ≥0 → ℝ := fun r =>
    X.X r ω - Function.leftLim (fun a : ℝ≥0 => X.X a ω) r
  let W : ℝ≥0 → ℝ := fun r =>
    if (r : ℝ≥0∞) < ruinTime X x D ω then
      x + X.X r ω - rightLimit D r ω
    else riskProcess X x D r ω
  let cash : ℝ≥0 → ℝ := fun r =>
    if (r : ℝ≥0∞) < ruinTime X x D ω then
      rightLimit D r ω - D r ω else 0
  apply Finset.sum_le_sum
  intro r hr
  by_cases hs : (r : ℝ≥0∞) ≤ ruinTime X x D ω
  · simp only [if_pos hs]
    by_cases hb : Y r ∈ Icc (u + ζ) v
    · have hmember := (hS r).mp hr
      have hrpos : 0 < r :=
        lt_of_le_of_lt (show (0 : ℝ≥0) ≤ s from zero_le) hmember.1
      have hrt : r ≤ t := hmember.2.1
      have hrneg : J r < 0 := hBneg hmember.2.2
      have hb' : Function.leftLim
          (fun a : ℝ≥0 => x + X.X a ω - rightLimit D a ω) r ∈
            Icc (u + ζ) v := hb
      have hsingle :=
        avram_wave5_03_canonical_hjump_inclusive_ruin_source_discounted_jump_bound
          X x D hD w hjump
          ω t r hrpos hrt hs q u v ζ hrneg hb
      simpa only [if_pos hb'] using hsingle
    · have hb' : ¬ Function.leftLim
          (fun a : ℝ≥0 => x + X.X a ω - rightLimit D a ω) r ∈
            Icc (u + ζ) v := hb
      simpa only [if_neg hb'] using (le_refl (0 : ℝ))
  · simp only [if_neg hs]
    exact le_refl _