-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18_original_all_mesh_clocks_full_threechannel_discounted_reward
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T20:33:22.207412+00:00
-- url     : https://prove2.me/submissions/510ef998-9ecb-4f26-8765-441221c76e27

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_ja18_original_discounted_ruinclipped_full_threechannel_reward
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
/-- A single conull event carries the full original stopped reward for each mesh clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (w : ℝ → ℝ) (D : ℝ≥0 → Ω → ℝ)
    (τ : ℕ → Ω → ℝ≥0) (F : ℕ → Ω → ℝ)
    (hFsource : ∀ k ω, F k ω =
      Real.exp (-(q * (τ k ω : ℝ))) *
        w (if τ k ω = 0 ∨ (τ k ω : ℝ≥0∞) < ruinTime X x D ω
          then x + X.X (τ k ω) ω - rightLimit D (τ k ω) ω
          else riskProcess X x D (τ k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ k ω : ℝ),
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
    ∀ᵐ ω ∂P, ∀ k : ℕ, F k ω =
      Real.exp (-(q * (τ k ω : ℝ))) *
        w (x + (τ k ω : ℝ) * X.c + R (τ k ω) ω + Jsmall (τ k ω) ω +
          avram_p4_h_gaussian_intrinsic_large_jump_sum X (τ k ω) ω -
          (if τ k ω = 0 ∨ (τ k ω : ℝ≥0∞) < ruinTime X x D ω
           then rightLimit D (τ k ω) ω else D (τ k ω) ω)) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal := by
  rw [ae_all_iff]
  intro k
  exact avram_ja18_original_discounted_ruinclipped_full_threechannel_reward
    X q x w D (τ k) (F k) (hFsource k) R Jsmall hR hJ
