-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_stopped_L2_error_bound_gives_L1_convergence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:17:31.991818+00:00
-- url     : https://prove2.me/submissions/a90fd127-47cd-4fe9-8602-6135c3424f70

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_nonnegative_integral_tendsto_of_uniform_second_moment
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Uniform L² error energy yields genuine L¹ convergence for original stopped residuals.
    No pathwise common dominating random variable is needed. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (Mk : ℕ → Ω → ℝ) (M : Ω → ℝ)
    (hDiffMeas : ∀ k, AEStronglyMeasurable
      (fun ω => ‖Mk k ω - M ω‖) P)
    (hAs : ∀ᵐ ω ∂P, Tendsto (fun k => Mk k ω) atTop (𝓝 (M ω)))
    (C : ℝ) (hC : 0 ≤ C)
    (hDiffSq : ∀ k, Integrable (fun ω => (‖Mk k ω - M ω‖) ^ 2) P ∧
      (∫ ω, (‖Mk k ω - M ω‖) ^ 2 ∂P) ≤ C) :
    Tendsto (fun k => ∫ ω, ‖Mk k ω - M ω‖ ∂P)
      atTop (𝓝 (0 : ℝ)) := by
  have hNonneg : ∀ k, ∀ᵐ ω ∂P, 0 ≤ ‖Mk k ω - M ω‖ := by
    intro k
    exact Filter.Eventually.of_forall (fun ω => norm_nonneg _)
  have hConv : ∀ᵐ ω ∂P,
      Tendsto (fun k => ‖Mk k ω - M ω‖) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hAs] with ω hw
    have hZero := (hw.sub_const (M ω)).norm
    simpa only [sub_self, norm_zero] using hZero
  obtain ⟨_, hLim⟩ :=
    nonnegative_integral_tendsto_of_uniform_second_moment
      (fun k ω => ‖Mk k ω - M ω‖) (fun _ => (0 : ℝ))
      hDiffMeas hNonneg aestronglyMeasurable_const hConv C hC hDiffSq
  simpa only [integral_zero] using hLim