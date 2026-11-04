-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_ae_norm_bound_passes_to_stopped_residual_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:13:05.19163+00:00
-- url     : https://prove2.me/submissions/0d42e05c-f3b7-458d-ab5e-3a223b905111

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open AvramDividend.Classical

/-- A common samplewise bound passes to the a.s. limit of original stopped residuals. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (Mk : ℕ → Ω → ℝ) (M B : Ω → ℝ)
    (hBound : ∀ k, ∀ᵐ ω ∂P, ‖Mk k ω‖ ≤ B ω)
    (hAs : ∀ᵐ ω ∂P, Tendsto (fun k => Mk k ω) atTop (𝓝 (M ω))) :
    ∀ᵐ ω ∂P, ‖M ω‖ ≤ ‖B ω‖ := by
  have hAll : ∀ᵐ ω ∂P, ∀ k, ‖Mk k ω‖ ≤ B ω :=
    ae_all_iff.mpr hBound
  filter_upwards [hAll, hAs] with ω hω hlim
  have hnorm : Tendsto (fun k => ‖Mk k ω‖) atTop (𝓝 ‖M ω‖) :=
    (continuous_norm.tendsto (M ω)).comp hlim
  have hle : ‖M ω‖ ≤ B ω := le_of_tendsto hnorm (Filter.Eventually.of_forall hω)
  exact hle.trans (le_abs_self (B ω))
