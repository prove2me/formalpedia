-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_true_postpayment_reserve_rightmesh_converges
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T16:07:13.045408+00:00
-- url     : https://prove2.me/submissions/8d5a7479-2a6b-4e1f-a59e-8fbd643b9724

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_postpayment_reserve_rightContinuous
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_rightmesh_continuous_within_clock
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (τ : Ω → ℝ≥0) (σ : ℕ → Ω → ℝ≥0)
    (hσle : ∀ k ω, σ k ω ≤ τ ω)
    (k : ℕ) (ω : Ω) :
    Tendsto (fun m : ℕ =>
      x + X.X (min (τ ω) (σ k ω +
        (1 : ℝ≥0) / ((m : ℝ≥0) + 1))) ω -
        rightLimit D (min (τ ω) (σ k ω +
          (1 : ℝ≥0) / ((m : ℝ≥0) + 1))) ω)
      atTop (𝓝 (x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω)) := by
  exact avram_f6_original_rightmesh_continuous_within_clock
    (σ k ω) (τ ω) (hσle k ω)
    (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω)
    (avram_wave8_20_original_postpayment_reserve_rightContinuous
      X x D hD ω (σ k ω))
