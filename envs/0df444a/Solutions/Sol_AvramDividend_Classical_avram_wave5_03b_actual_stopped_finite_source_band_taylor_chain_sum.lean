-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03b_actual_stopped_finite_source_band_taylor_chain_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T08:41:30.818675+00:00
-- url     : https://prove2.me/submissions/abc25cc8-0591-4d0d-a173-c025726bf050

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_source_taylor_generator_kernel_eq

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Exact source-X finite-band stopped chain rule: the controlled prepayment
nonlinear source jumps equal their Lévy-truncated linear plus generator sums.
Right dividend payments remain chronological and separate. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (u v δ : ℝ)
    (s t : ℝ≥0) (ω : Ω)
    (B : Set ℝ) (hBneg : B ⊆ Iio (0 : ℝ))
    (T : Finset ℝ≥0)
    (hT : ∀ q : ℝ≥0, q ∈ T ↔
      s < q ∧ q ≤ t ∧
        X.X q ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) q ∈ B) :
    let Y : ℝ≥0 → ℝ := fun q => Function.leftLim
      (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) q
    let J : ℝ≥0 → ℝ := fun q =>
      X.X q ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) q
    (∑ q ∈ T, if (q : ℝ≥0∞) ≤ ruinTime X x D ω then
      (if Y q ∈ Icc (u + δ) v then
        w (Y q + J q) - w (Y q) else 0) else 0) =
    (∑ q ∈ T, if (q : ℝ≥0∞) ≤ ruinTime X x D ω then
      (if -1 < J q then
        J q * (if Y q ∈ Icc (u + δ) v then deriv w (Y q) else 0)
        else 0) +
      (if Y q ∈ Icc (u + δ) v then
        SpectrallyNegativeLevy.generatorIntegrand w (Y q) (J q)
        else 0) else 0) := by
  let Y : ℝ≥0 → ℝ := fun q => Function.leftLim
    (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) q
  let J : ℝ≥0 → ℝ := fun q =>
    X.X q ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) q
  change
    (∑ q ∈ T, if (q : ℝ≥0∞) ≤ ruinTime X x D ω then
      (if Y q ∈ Icc (u + δ) v then
        w (Y q + J q) - w (Y q) else 0) else 0) =
    (∑ q ∈ T, if (q : ℝ≥0∞) ≤ ruinTime X x D ω then
      (if -1 < J q then
        J q * (if Y q ∈ Icc (u + δ) v then deriv w (Y q) else 0)
        else 0) +
      (if Y q ∈ Icc (u + δ) v then
        SpectrallyNegativeLevy.generatorIntegrand w (Y q) (J q)
        else 0) else 0)
  classical
  apply Finset.sum_congr rfl
  intro q hq
  have hqB : J q ∈ B := by
    have hqdata := (hT q).mp hq
    exact hqdata.2.2
  have hz : J q < 0 := hBneg hqB
  have hid :=
    avram_wave5_03b_actual_source_taylor_generator_kernel_eq
      X x D hD w u v δ (q, ω) (J q) hz
  change
    (if Y q ∈ Icc (u + δ) v then
      w (Y q + J q) - w (Y q) else 0) -
    (if -1 < J q then
      J q * (if Y q ∈ Icc (u + δ) v then deriv w (Y q) else 0)
      else 0) =
    (if Y q ∈ Icc (u + δ) v then
      SpectrallyNegativeLevy.generatorIntegrand w (Y q) (J q)
      else 0) at hid
  by_cases hstop : (q : ℝ≥0∞) ≤ ruinTime X x D ω
  · simp only [if_pos hstop]
    linarith [hid]
  · simp [hstop]
