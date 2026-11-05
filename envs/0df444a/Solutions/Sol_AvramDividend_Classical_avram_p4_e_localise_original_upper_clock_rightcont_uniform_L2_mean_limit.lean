-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_upper_clock_rightcont_uniform_L2_mean_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:45:36.860483+00:00
-- url     : https://prove2.me/submissions/5d237c08-edbe-40bc-8a60-53a661dc6d40

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_rightcont_residual_ceiling_values_ae_tendsto
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_L2_two_sided_signed_martingale_mean_limit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Genuine two-sided L2 estimates and right-continuous original clock limits give a centred L1 residual. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (u : ℕ → Ω → ℝ≥0)
    (hClock : ∀ ω, Tendsto (fun k => u k ω) atTop (𝓝 (τ ω)))
    (hAbove : ∀ k ω, τ ω ≤ u k ω)
    (f : ℝ≥0 → Ω → ℝ)
    (hRight : ∀ᵐ ω ∂P, ContinuousWithinAt (fun t => f t ω)
      (Set.Ici (τ ω)) (τ ω))
    (hPosMeas : ∀ k, AEStronglyMeasurable
      (fun ω => max (f (u k ω) ω) 0) P)
    (hNegMeas : ∀ k, AEStronglyMeasurable
      (fun ω => max (-(f (u k ω) ω)) 0) P)
    (hPosMMeas : AEStronglyMeasurable
      (fun ω => max (f (τ ω) ω) 0) P)
    (hNegMMeas : AEStronglyMeasurable
      (fun ω => max (-(f (τ ω) ω)) 0) P)
    (C : ℝ) (hC : 0 ≤ C)
    (hPos2 : ∀ k, Integrable
      (fun ω => (max (f (u k ω) ω) 0) ^ 2) P ∧
      (∫ ω, (max (f (u k ω) ω) 0) ^ 2 ∂P) ≤ C)
    (hNeg2 : ∀ k, Integrable
      (fun ω => (max (-(f (u k ω) ω)) 0) ^ 2) P ∧
      (∫ ω, (max (-(f (u k ω) ω)) 0) ^ 2 ∂P) ≤ C)
    (hSplit : ∀ k,
      (∫ ω, max (f (u k ω) ω) 0 ∂P) -
      (∫ ω, max (-(f (u k ω) ω)) 0 ∂P) = 0) :
    Integrable (fun ω => f (τ ω) ω) P ∧
      (∫ ω, f (τ ω) ω ∂P) = 0 := by
  have hAs := avram_p4_e_localise_original_rightcont_residual_ceiling_values_ae_tendsto
    X x D n τ hτeq f u hClock hAbove hRight
  have hPosConv : ∀ᵐ ω ∂P,
      Tendsto (fun k => max (f (u k ω) ω) 0)
        atTop (𝓝 (max (f (τ ω) ω) 0)) := by
    filter_upwards [hAs] with ω h
    exact h.max tendsto_const_nhds
  have hNegConv : ∀ᵐ ω ∂P,
      Tendsto (fun k => max (-(f (u k ω) ω)) 0)
        atTop (𝓝 (max (-(f (τ ω) ω)) 0)) := by
    filter_upwards [hAs] with ω h
    exact h.neg.max tendsto_const_nhds
  exact avram_p4_e_localise_original_L2_two_sided_signed_martingale_mean_limit
    X (fun k ω => f (u k ω) ω) (fun ω => f (τ ω) ω)
    hPosMeas hNegMeas hPosMMeas hNegMMeas
    hPosConv hNegConv C hC hPos2 hNeg2 hSplit
