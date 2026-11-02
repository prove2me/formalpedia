-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03b_actual_centered_source_intrinsic_nonlinear_stopped_ito_band_balance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T18:04:50.679711+00:00
-- url     : https://prove2.me/submissions/b0ce459f-2417-47fc-933d-54821984858c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_stopped_nonlinear_source_intrinsic_ito_band_balance
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_source_C2_generator_time_integrated_jump_drift_eq

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- Exact centred finite-band jump chain balance for the actual source Lévy
marks and adapted controlled prepayment reserve; no martingale claim. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C)
    (s t : ℝ≥0) (ω : Ω)
    (B : Set ℝ) (hBm : MeasurableSet B)
    (hBneg : B ⊆ Iio (0 : ℝ))
    (ε : ℝ) (hε : 0 < ε)
    (hBsep : ∀ z ∈ B, ε ≤ dist z 0)
    (μ : Measure ℝ≥0) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun r : ℝ≥0 => x + X.X r p.2 - rightLimit D r p.2) p.1
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if Y p.1 ∈ Icc (u + δ) v then
        w (Y p.1 + p.2) - w (Y p.1) else 0) -
      (if -1 < p.2 then
        p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0)
        else 0)
    let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * H p
    let J : ℝ≥0 → Ω → ℝ := fun r η =>
      X.X r η - Function.leftLim (fun z : ℝ≥0 => X.X z η) r
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun η =>
      ((Measure.count.restrict {r : ℝ≥0 | 0 < r ∧ J r η ≠ 0}).map
        (fun r : ℝ≥0 => (r, J r η)))
    let G : ℝ≥0 × ℝ → ℝ := fun p =>
      if s < p.1 ∧ p.1 ≤ t ∧ p.2 ∈ B then HS ((p.1,ω),p.2) else 0
    let L : ℝ≥0 → ℝ := fun r =>
      if -1 < J r ω then
        J r ω * (if Y (r,ω) ∈ Icc (u + δ) v then deriv w (Y (r,ω)) else 0)
      else 0
    let S : ℝ≥0 → ℝ := fun r =>
      if (r : ℝ≥0∞) ≤ ruinTime X x D ω then 1 else 0
    let Drift : ℝ≥0 → ℝ := fun r =>
      ∫ z in B, S r * H ((r,ω),z) ∂X.ν
    let Gen : ℝ≥0 → ℝ := fun r =>
      ∫ z in B, S r *
        (if Y (r,ω) ∈ Icc (u + δ) v then
          SpectrallyNegativeLevy.generatorIntegrand w (Y (r,ω)) z else 0) ∂X.ν
    ∃ T : Finset ℝ≥0,
      (∀ r : ℝ≥0, r ∈ T ↔ s < r ∧ r ≤ t ∧ J r ω ∈ B) ∧
      Integrable G (NX ω) ∧
      ((∑ r ∈ T, if (r : ℝ≥0∞) ≤ ruinTime X x D ω then
        (if Y (r,ω) ∈ Icc (u + δ) v then
          w (riskProcess X x D r ω) -
          w (Function.leftLim (fun q : ℝ≥0 => riskProcess X x D q ω) r)
        else 0) else 0) -
        (∫ r in Ioc s t, Drift r ∂μ)) =
      (∑ r ∈ T, if (r : ℝ≥0∞) ≤ ruinTime X x D ω then L r else 0) +
        ((∫ p : ℝ≥0 × ℝ, G p ∂NX ω) -
        (∫ r in Ioc s t, Gen r ∂μ)) := by
  let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
    (fun r : ℝ≥0 => x + X.X r p.2 - rightLimit D r p.2) p.1
  let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
    (if Y p.1 ∈ Icc (u + δ) v then
      w (Y p.1 + p.2) - w (Y p.1) else 0) -
    (if -1 < p.2 then
      p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0)
      else 0)
  let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
    (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * H p
  let J : ℝ≥0 → Ω → ℝ := fun r η =>
    X.X r η - Function.leftLim (fun z : ℝ≥0 => X.X z η) r
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun η =>
    ((Measure.count.restrict {r : ℝ≥0 | 0 < r ∧ J r η ≠ 0}).map
      (fun r : ℝ≥0 => (r, J r η)))
  let G : ℝ≥0 × ℝ → ℝ := fun p =>
    if s < p.1 ∧ p.1 ≤ t ∧ p.2 ∈ B then HS ((p.1,ω),p.2) else 0
  let L : ℝ≥0 → ℝ := fun r =>
    if -1 < J r ω then
      J r ω * (if Y (r,ω) ∈ Icc (u + δ) v then deriv w (Y (r,ω)) else 0)
    else 0
  let S : ℝ≥0 → ℝ := fun r =>
    if (r : ℝ≥0∞) ≤ ruinTime X x D ω then 1 else 0
  let Drift : ℝ≥0 → ℝ := fun r =>
    ∫ z in B, S r * H ((r,ω),z) ∂X.ν
  let Gen : ℝ≥0 → ℝ := fun r =>
    ∫ z in B, S r *
      (if Y (r,ω) ∈ Icc (u + δ) v then
        SpectrallyNegativeLevy.generatorIntegrand w (Y (r,ω)) z else 0) ∂X.ν
  change ∃ T : Finset ℝ≥0, (∀ r : ℝ≥0, r ∈ T ↔
      s < r ∧ r ≤ t ∧ J r ω ∈ B) ∧ Integrable G (NX ω) ∧
      ((∑ r ∈ T, if (r : ℝ≥0∞) ≤ ruinTime X x D ω then
        (if Y (r,ω) ∈ Icc (u + δ) v then
          w (riskProcess X x D r ω) -
          w (Function.leftLim (fun q : ℝ≥0 => riskProcess X x D q ω) r)
        else 0) else 0) - (∫ r in Ioc s t, Drift r ∂μ)) =
      (∑ r ∈ T, if (r : ℝ≥0∞) ≤ ruinTime X x D ω then L r else 0) +
        ((∫ p : ℝ≥0 × ℝ, G p ∂NX ω) - (∫ r in Ioc s t, Gen r ∂μ))
  obtain ⟨T, hT, hGi, hBal⟩ :=
    avram_wave5_03b_actual_stopped_nonlinear_source_intrinsic_ito_band_balance
      X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv
      s t ω B hBm hBneg ε hε hBsep
  refine ⟨T, hT, hGi, ?_⟩
  have hDrift : (∫ r in Ioc s t, Drift r ∂μ) =
      (∫ r in Ioc s t, Gen r ∂μ) := by
    simpa [Drift, Gen, S, H, Y] using
      (avram_wave5_03b_actual_ruin_stopped_source_C2_generator_time_integrated_jump_drift_eq
        X x D hD w u v δ s t ω μ B hBm hBneg)
  rw [hBal, hDrift]
  ring
