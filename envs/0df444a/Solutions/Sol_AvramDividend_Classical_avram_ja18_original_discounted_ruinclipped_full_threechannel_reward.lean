-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18_original_discounted_ruinclipped_full_threechannel_reward
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T20:18:31.301881+00:00
-- url     : https://prove2.me/submissions/8a4a9f2c-3f80-4e8f-88d2-292e5fc5f774

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_ja18_original_ruinclipped_stopped_reserve_full_threechannel_source
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
/-- Actual stopped reward is evaluated on the full source and cash. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (w : ℝ → ℝ) (D : ℝ≥0 → Ω → ℝ)
    (τ : Ω → ℝ≥0) (F : Ω → ℝ)
    (hFsource : ∀ ω, F ω =
      Real.exp (-(q * (τ ω : ℝ))) *
        w (if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
          then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
          else riskProcess X x D (τ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (R Jsmall : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (nhds (R t ω)))
    (hJ : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
        atTop (nhds (Jsmall t ω))) :
    ∀ᵐ ω ∂P, F ω =
      Real.exp (-(q * (τ ω : ℝ))) *
        w (x + (τ ω : ℝ) * X.c + R (τ ω) ω + Jsmall (τ ω) ω +
          avram_p4_h_gaussian_intrinsic_large_jump_sum X (τ ω) ω -
          (if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
           then rightLimit D (τ ω) ω else D (τ ω) ω)) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal := by
  let W : Ω → ℝ := fun ω =>
    if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
    then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
    else riskProcess X x D (τ ω) ω
  have hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω := by
    intro ω
    rfl
  have hs := avram_ja18_original_ruinclipped_stopped_reserve_full_threechannel_source
    X x D τ W hW R Jsmall hR hJ
  filter_upwards [hs] with ω hh
  rw [hFsource ω]
  change Real.exp (-(q * (τ ω : ℝ))) * w (W ω) +
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal = _
  rw [hh]
