-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_upper_clock_rightcont_centred_L1_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:36:55.530738+00:00
-- url     : https://prove2.me/submissions/89fc3bff-b7fe-4fc6-874d-1b7b523b494b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_rightcont_residual_ceiling_values_ae_tendsto
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_domination_preserves_martingale_mean

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A right-continuous original stopped residual inherits genuine L1 and zero mean from its upper clocks. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (u : ℕ → Ω → ℝ≥0)
    (hClock : ∀ ω, Tendsto (fun k => u k ω) atTop (𝓝 (τ ω)))
    (hAbove : ∀ k ω, τ ω ≤ u k ω)
    (f : ℝ≥0 → Ω → ℝ)
    (hRight : ∀ᵐ ω ∂P,
      ContinuousWithinAt (fun t => f t ω) (Set.Ici (τ ω)) (τ ω))
    (hMkMeas : ∀ k, AEStronglyMeasurable
      (fun ω => f (u k ω) ω) P)
    (hMMeas : AEStronglyMeasurable (fun ω => f (τ ω) ω) P)
    (B : Ω → ℝ) (hBint : Integrable B P)
    (hBound : ∀ k, ∀ᵐ ω ∂P, ‖f (u k ω) ω‖ ≤ B ω)
    (hLimitBound : ∀ᵐ ω ∂P, ‖f (τ ω) ω‖ ≤ ‖B ω‖)
    (hCentre : ∀ k, (∫ ω, f (u k ω) ω ∂P) = 0) :
    Integrable (fun ω => f (τ ω) ω) P ∧
      (∫ ω, f (τ ω) ω ∂P) = 0 := by
  have hAs := avram_p4_e_localise_original_rightcont_residual_ceiling_values_ae_tendsto
    X x D n τ hτeq f u hClock hAbove hRight
  exact avram_p4_e_localise_original_domination_preserves_martingale_mean
    X (fun k ω => f (u k ω) ω) (fun ω => f (τ ω) ω) B
    hMkMeas hMMeas hBint hBound hLimitBound hAs hCentre
