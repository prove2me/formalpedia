-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03b_actual_stopped_nonlinear_source_intrinsic_ito_band_balance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T15:36:29.113908+00:00
-- url     : https://prove2.me/submissions/63565589-5308-4eee-9393-632de30cb9cf

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_C2_signed_intrinsic_separated_band_eq_finite_source_sum
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_separated_source_band_stopped_ito_balance
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_source_taylor_generator_kernel_eq

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- On each actual original separated source band, the stopped nonlinear
reserve jump chain rule has its true signed intrinsic source-measure term. -/
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
    (hBsep : ∀ z ∈ B, ε ≤ dist z 0) :
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
    ∃ T : Finset ℝ≥0,
      (∀ r : ℝ≥0, r ∈ T ↔ s < r ∧ r ≤ t ∧ J r ω ∈ B) ∧
      Integrable G (NX ω) ∧
      (∑ r ∈ T, if (r : ℝ≥0∞) ≤ ruinTime X x D ω then
        (if Y (r,ω) ∈ Icc (u + δ) v then
          w (riskProcess X x D r ω) -
          w (Function.leftLim (fun q : ℝ≥0 => riskProcess X x D q ω) r)
        else 0) else 0) =
      (∑ r ∈ T, if (r : ℝ≥0∞) ≤ ruinTime X x D ω then L r else 0) +
      (∫ p : ℝ≥0 × ℝ, G p ∂NX ω) := by
  let Y : ℝ≥0 × Ω → ℝ := fun p =>
    Function.leftLim (fun r : ℝ≥0 => x + X.X r p.2 - rightLimit D r p.2) p.1
  let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
    (if Y p.1 ∈ Icc (u + δ) v then w (Y p.1 + p.2) - w (Y p.1) else 0) -
    (if -1 < p.2 then p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0) else 0)
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
    if -1 < J r ω then J r ω *
      (if Y (r,ω) ∈ Icc (u + δ) v then deriv w (Y (r,ω)) else 0) else 0
  let K : ℝ≥0 → ℝ := fun r =>
    if Y (r,ω) ∈ Icc (u + δ) v then
      SpectrallyNegativeLevy.generatorIntegrand w (Y (r,ω)) (J r ω) else 0
  change ∃ T : Finset ℝ≥0,
      (∀ r : ℝ≥0, r ∈ T ↔ s < r ∧ r ≤ t ∧ J r ω ∈ B) ∧
      Integrable G (NX ω) ∧
      (∑ r ∈ T, if (r : ℝ≥0∞) ≤ ruinTime X x D ω then
        (if Y (r,ω) ∈ Icc (u + δ) v then
          w (riskProcess X x D r ω) -
          w (Function.leftLim (fun q : ℝ≥0 => riskProcess X x D q ω) r)
        else 0) else 0) =
      (∑ r ∈ T, if (r : ℝ≥0∞) ≤ ruinTime X x D ω then L r else 0) +
      (∫ p : ℝ≥0 × ℝ, G p ∂NX ω)
  obtain ⟨T, hT, hInt, hSigned⟩ :=
    avram_wave5_03b_actual_ruin_stopped_C2_signed_intrinsic_separated_band_eq_finite_source_sum
      X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv
      s t ω B hBm hBneg ε hε hBsep
  obtain ⟨T', hT', hBalance⟩ :=
    avram_wave5_03b_actual_separated_source_band_stopped_ito_balance
      X x D hD w u v δ s t ω B hBneg ε hε hBsep
  have hT'eq : T' = T := by
    ext r
    exact (hT' r).trans (hT r).symm
  rw [hT'eq] at hBalance
  have hGen (r : ℝ≥0) (hr : r ∈ T) :
      H ((r,ω),J r ω) = K r := by
    have hrB : J r ω ∈ B := ((hT r).mp hr).2.2
    have hneg : J r ω < 0 := hBneg hrB
    simpa only [Y, H, J, K] using
      (avram_wave5_03b_actual_source_taylor_generator_kernel_eq
        X x D hD w u v δ (r,ω) (J r ω) hneg)
  have hHS (r : ℝ≥0) (hr : r ∈ T) :
      HS ((r,ω),J r ω) =
        if (r : ℝ≥0∞) ≤ ruinTime X x D ω then K r else 0 := by
    change (if (r : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0) *
      H ((r,ω),J r ω) = _
    rw [hGen r hr]
    split_ifs <;> simp
  have hsplit (r : ℝ≥0) (hr : r ∈ T) :
      (if (r : ℝ≥0∞) ≤ ruinTime X x D ω then L r + K r else 0) =
      (if (r : ℝ≥0∞) ≤ ruinTime X x D ω then L r else 0) +
      HS ((r,ω),J r ω) := by
    rw [hHS r hr]
    split_ifs <;> simp
  refine ⟨T, hT, hInt, ?_⟩
  calc
    (∑ r ∈ T, if (r : ℝ≥0∞) ≤ ruinTime X x D ω then
      (if Y (r,ω) ∈ Icc (u + δ) v then
        w (riskProcess X x D r ω) -
        w (Function.leftLim (fun q : ℝ≥0 => riskProcess X x D q ω) r)
      else 0) else 0) =
      (∑ r ∈ T, if (r : ℝ≥0∞) ≤ ruinTime X x D ω then L r + K r else 0) := by
        simpa only [Y, J, L, K] using hBalance
    _ = (∑ r ∈ T,
      ((if (r : ℝ≥0∞) ≤ ruinTime X x D ω then L r else 0) +
      HS ((r,ω),J r ω))) := by
        apply Finset.sum_congr rfl
        intro r hr
        exact hsplit r hr
    _ = (∑ r ∈ T, if (r : ℝ≥0∞) ≤ ruinTime X x D ω then L r else 0) +
      ∑ r ∈ T, HS ((r,ω),J r ω) := Finset.sum_add_distrib
    _ = _ := by rw [hSigned]
