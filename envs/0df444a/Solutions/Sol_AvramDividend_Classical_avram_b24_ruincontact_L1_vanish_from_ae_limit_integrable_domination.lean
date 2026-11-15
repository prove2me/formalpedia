-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_ruincontact_L1_vanish_from_ae_limit_integrable_domination
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T13:59:26.042029+00:00
-- url     : https://prove2.me/submissions/42ba753b-a7c1-4bcc-a98d-9c562144e941

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (F : ℕ → Ω → ℝ) (B : Ω → ℝ)
    (hFI : ∀ k, Integrable (F k) P)
    (hBI : Integrable B P)
    (hBound : ∀ k, ∀ᵐ ω ∂P, ‖F k ω‖ ≤ B ω)
    (hLim : ∀ᵐ ω ∂P, Tendsto (fun k => F k ω) atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun k => ∫ ω, ‖F k ω‖ ∂P) atTop (𝓝 (0 : ℝ)) := by
  have hMeas (k : ℕ) :
      AEStronglyMeasurable (fun ω => ‖F k ω‖) P :=
    (hFI k).norm.aestronglyMeasurable
  have hDom (k : ℕ) :
      ∀ᵐ ω ∂P, ‖‖F k ω‖‖ ≤ B ω := by
    filter_upwards [hBound k] with ω hw
    simpa only [norm_norm] using hw
  have hNormLim : ∀ᵐ ω ∂P,
      Tendsto (fun k => ‖F k ω‖) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hLim] with ω hω
    simpa only [norm_zero] using hω.norm
  have hDCT :=
    tendsto_integral_of_dominated_convergence B hMeas hBI hDom hNormLim
  simpa only [integral_zero] using hDCT
