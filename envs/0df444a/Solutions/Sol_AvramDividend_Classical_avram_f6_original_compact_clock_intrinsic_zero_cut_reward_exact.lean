-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_compact_clock_intrinsic_zero_cut_reward_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T08:12:21.532055+00:00
-- url     : https://prove2.me/submissions/a299feff-9f5d-495d-bbae-58f2055d6634

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_stopped_W_sameX_intrinsic_residual
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_stopped_W_sameX_intrinsic_residual
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated_zero_cutoff
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (w : ℝ → ℝ) (D : ℝ≥0 → Ω → ℝ)
    (σ : ℕ → Ω → ℝ≥0) (F : ℕ → Ω → ℝ)
    (hFsource : ∀ k ω, F k ω =
      Real.exp (-(q * (σ k ω : ℝ))) *
        w (if σ k ω = 0 ∨
              (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
          else riskProcess X x D (σ k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    :
    ∀ k ω, F k ω =
      Real.exp (-(q * (σ k ω : ℝ))) *
        w (x + (σ k ω : ℝ) * X.c +
          avram_p4_h_gaussian_intrinsic_large_jump_sum X (σ k ω) ω +
          avram_p4_h_gaussian_intrinsic_truncated_residual X 0 (σ k ω) ω -
          (if σ k ω = 0 ∨ (σ k ω : ℝ≥0∞) < ruinTime X x D ω
           then rightLimit D (σ k ω) ω else D (σ k ω) ω)) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal := by
  intro k ω
  let W : Ω → ℝ := fun η =>
    if σ k η = 0 ∨ (σ k η : ℝ≥0∞) < ruinTime X x D η then
      x + X.X (σ k η) η - rightLimit D (σ k η) η
    else riskProcess X x D (σ k η) η
  have hW : ∀ η, W η =
      if σ k η = 0 ∨ (σ k η : ℝ≥0∞) < ruinTime X x D η then
        x + X.X (σ k η) η - rightLimit D (σ k η) η
      else riskProcess X x D (σ k η) η := by
    intro η
    rfl
  have hSource :=
    avram_p4_f3_original_stopped_W_sameX_intrinsic_residual
      X x D 0 (σ k) W hW ω
  have hWeighted := congrArg
    (fun v : ℝ =>
      Real.exp (-(q * (σ k ω : ℝ))) * w v +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal)
    hSource
  simpa only [W, hFsource k ω,
    avram_p4_h_gaussian_intrinsic_small_band_compensated_zero_cutoff,
    add_zero] using hWeighted
