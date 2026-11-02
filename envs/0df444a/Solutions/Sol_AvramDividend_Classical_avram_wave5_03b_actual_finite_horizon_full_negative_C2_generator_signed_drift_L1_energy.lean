-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03b_actual_finite_horizon_full_negative_C2_generator_signed_drift_L1_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T11:13:47.614765+00:00
-- url     : https://prove2.me/submissions/c2549f98-91df-41cd-87f1-bf60c64f5337

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_finite_horizon_full_negative_C2_source_physical_L1_L2_energy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_source_generator_jump_drift_integral_eq

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Finite original-P expected absolute full negative Lévy generator jump drift
for the original dividend-controlled and ruin-stopped prepayment reserve. -/
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
    (T : ℝ≥0) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let JG : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) *
      (if Y p.1 ∈ Icc (u + δ) v then
        SpectrallyNegativeLevy.generatorIntegrand w (Y p.1) p.2 else 0)
    (∫⁻ p : ℝ≥0 × Ω,
      ‖∫ z in Iio (0 : ℝ), JG (p,z) ∂X.ν‖ₑ ∂
      (((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) < ⊤ := by
  let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
    (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
  let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
    (if Y p.1 ∈ Icc (u + δ) v then
      w (Y p.1 + p.2) - w (Y p.1) else 0) -
    (if -1 < p.2 then
      p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0)
      else 0)
  let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
    (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * H p
  let JG : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
    (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) *
    (if Y p.1 ∈ Icc (u + δ) v then
      SpectrallyNegativeLevy.generatorIntegrand w (Y p.1) p.2 else 0)
  change (∫⁻ p : ℝ≥0 × Ω,
      ‖∫ z in Iio (0 : ℝ), JG (p,z) ∂X.ν‖ₑ ∂
      (((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) < ⊤
  have hfull :=
    (avram_wave5_03b_actual_finite_horizon_full_negative_C2_source_physical_L1_L2_energy
      X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv T).1
  have heq (p : ℝ≥0 × Ω) :
      (∫ z in Iio (0 : ℝ), HS (p,z) ∂X.ν) =
      (∫ z in Iio (0 : ℝ), JG (p,z) ∂X.ν) := by
    simpa [HS, H, JG, Y] using
      (avram_wave5_03b_actual_ruin_stopped_source_generator_jump_drift_integral_eq
        X x D hD w u v δ p (Iio (0 : ℝ))
        measurableSet_Iio (Subset.rfl))
  have hpoint (p : ℝ≥0 × Ω) :
      ‖∫ z in Iio (0 : ℝ), JG (p,z) ∂X.ν‖ₑ ≤
        ∫⁻ z in Iio (0 : ℝ), ENNReal.ofReal (|HS (p,z)|) ∂X.ν := by
    rw [← heq p]
    simpa only [Real.enorm_eq_ofReal_abs] using
      (enorm_integral_le_lintegral_enorm
        (μ := X.ν.restrict (Iio (0 : ℝ))) (fun z : ℝ => HS (p,z)))
  exact lt_of_le_of_lt (lintegral_mono hpoint) hfull
