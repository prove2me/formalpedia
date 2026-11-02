-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03_original_stopped_finite_source_jump_right_payment_chronological_merge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T15:11:27.151804+00:00
-- url     : https://prove2.me/submissions/3e708229-26ef-431c-b018-be237098d9a2

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_stopped_finite_source_band_taylor_chain_sum
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_original_prepost_reserve_same_leftlim
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_original_prepayment_reserve_exact_source_jumpmark

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- At every positive source jump within one actual finite Lévy mark band, the
full stopped post-payment nonlinear increment splits into the exact source
Taylor drift/mark part and a separate simultaneous right-dividend value drop.
No assumption of disjoint jump and payment clocks is made. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (u v δ : ℝ)
    (s t : ℝ≥0) (ω : Ω)
    (B : Set ℝ) (hBneg : B ⊆ Iio (0 : ℝ))
    (S : Finset ℝ≥0)
    (hS : ∀ r : ℝ≥0, r ∈ S ↔
      s < r ∧ r ≤ t ∧
        X.X r ω - Function.leftLim (fun a : ℝ≥0 => X.X a ω) r ∈ B) :
    let Y : ℝ≥0 → ℝ := fun r => Function.leftLim
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
          w (riskProcess X x D r ω) else 0) else 0) := by
  classical
  let Y : ℝ≥0 → ℝ := fun r => Function.leftLim
    (fun a : ℝ≥0 => x + X.X a ω - rightLimit D a ω) r
  let J : ℝ≥0 → ℝ := fun r =>
    X.X r ω - Function.leftLim (fun a : ℝ≥0 => X.X a ω) r
  change
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
          w (riskProcess X x D r ω) else 0) else 0)
  have hpre (r : ℝ≥0) (hr : r ∈ S) :
      riskProcess X x D r ω = Y r + J r := by
    have hrpos : (0 : ℝ≥0) < r :=
      lt_of_le_of_lt (show (0 : ℝ≥0) ≤ s from zero_le) ((hS r).mp hr).1
    have hmark :=
      avram_wave4_p2_original_prepayment_reserve_exact_source_jumpmark
        X x D hD ω r hrpos
    have hleft :=
      avram_wave4_p2_original_prepost_reserve_same_leftlim
        X x D hD ω r hrpos
    calc
      riskProcess X x D r ω =
        Function.leftLim
          (fun a : ℝ≥0 => riskProcess X x D a ω) r +
          (X.X r ω -
            Function.leftLim (fun a : ℝ≥0 => X.X a ω) r) := by
          linarith
      _ = Y r + J r := by rw [hleft]
  have hsource :
      (∑ r ∈ S, if (r : ℝ≥0∞) ≤ ruinTime X x D ω then
        (if Y r ∈ Icc (u + δ) v then
          w (Y r + J r) - w (Y r) else 0) else 0) =
      (∑ r ∈ S, if (r : ℝ≥0∞) ≤ ruinTime X x D ω then
        (if -1 < J r then
          J r * (if Y r ∈ Icc (u + δ) v then deriv w (Y r) else 0)
          else 0) +
        (if Y r ∈ Icc (u + δ) v then
          SpectrallyNegativeLevy.generatorIntegrand w (Y r) (J r)
          else 0) else 0) := by
    simpa only [Y, J] using
      avram_wave5_03b_actual_stopped_finite_source_band_taylor_chain_sum
        X x D hD w u v δ s t ω B hBneg S hS
  have hsplit :
      (∑ r ∈ S, if (r : ℝ≥0∞) ≤ ruinTime X x D ω then
        (if Y r ∈ Icc (u + δ) v then
          w (riskProcess X x D r ω -
            (rightLimit D r ω - D r ω)) - w (Y r) else 0) else 0) =
      (∑ r ∈ S, if (r : ℝ≥0∞) ≤ ruinTime X x D ω then
        (if Y r ∈ Icc (u + δ) v then
          w (Y r + J r) - w (Y r) else 0) else 0) +
      (∑ r ∈ S, if (r : ℝ≥0∞) ≤ ruinTime X x D ω then
        (if Y r ∈ Icc (u + δ) v then
          w (riskProcess X x D r ω -
            (rightLimit D r ω - D r ω)) -
            w (riskProcess X x D r ω) else 0) else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    have hR := hpre r hr
    by_cases hstop : (r : ℝ≥0∞) ≤ ruinTime X x D ω
    · rw [if_pos hstop, if_pos hstop, if_pos hstop]
      by_cases hband : Y r ∈ Icc (u + δ) v
      · rw [if_pos hband, if_pos hband, if_pos hband, ← hR]
        ring
      · rw [if_neg hband, if_neg hband, if_neg hband]
        ring
    · rw [if_neg hstop, if_neg hstop, if_neg hstop]
      ring
  rw [hsource] at hsplit
  exact hsplit
