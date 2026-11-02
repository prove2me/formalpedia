-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03_original_stopped_separated_source_jump_right_payment_full_band_balance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T15:18:13.244376+00:00
-- url     : https://prove2.me/submissions/2b7b37c7-2f0e-4b87-9549-8c787acf5b5c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_separated_source_band_stopped_ito_balance
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_stopped_finite_source_jump_right_payment_chronological_merge

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- Existence of an actual finite original-source enumeration, plus the exact
ruin-stopped source jump and simultaneous right-dividend nonlinear balance. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (u v δ : ℝ)
    (s t : ℝ≥0) (ω : Ω)
    (B : Set ℝ) (hBneg : B ⊆ Iio (0 : ℝ))
    (ε : ℝ) (hε : 0 < ε)
    (hBsep : ∀ z ∈ B, ε ≤ dist z 0) :
    ∃ S : Finset ℝ≥0,
      (∀ r : ℝ≥0, r ∈ S ↔
        s < r ∧ r ≤ t ∧
          X.X r ω - Function.leftLim (fun a : ℝ≥0 => X.X a ω) r ∈ B) ∧
      (let Y : ℝ≥0 → ℝ := fun r => Function.leftLim
          (fun a : ℝ≥0 => x + X.X a ω - rightLimit D a ω) r
       let J : ℝ≥0 → ℝ := fun r =>
          X.X r ω - Function.leftLim (fun a : ℝ≥0 => X.X a ω) r
       (∑ r ∈ S, if (r : ℝ≥0∞) ≤ ruinTime X x D ω then
         (if Y r ∈ Icc (u + δ) v then
           w (riskProcess X x D r ω -
             (rightLimit D r ω - D r ω)) - w (Y r) else 0) else 0) =
       (∑ r ∈ S, if (r : ℝ≥0∞) ≤ ruinTime X x D ω then
         (if -1 < J r then
           J r * (if Y r ∈ Icc (u + δ) v then deriv w (Y r) else 0)
           else 0) +
         (if Y r ∈ Icc (u + δ) v then
           SpectrallyNegativeLevy.generatorIntegrand w (Y r) (J r)
           else 0) else 0) +
       (∑ r ∈ S, if (r : ℝ≥0∞) ≤ ruinTime X x D ω then
         (if Y r ∈ Icc (u + δ) v then
           w (riskProcess X x D r ω -
             (rightLimit D r ω - D r ω)) -
             w (riskProcess X x D r ω) else 0) else 0)) := by
  classical
  obtain ⟨S, hS, _⟩ :=
    avram_wave5_03b_actual_separated_source_band_stopped_ito_balance
      X x D hD w u v δ s t ω B hBneg ε hε hBsep
  exact ⟨S, hS,
    avram_wave5_03_original_stopped_finite_source_jump_right_payment_chronological_merge
      X x D hD w u v δ s t ω B hBneg S hS⟩
