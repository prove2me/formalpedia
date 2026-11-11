-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18_integrable_of_dom_ae_grid_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T21:45:14.277638+00:00
-- url     : https://prove2.me/submissions/8f9b28ec-837e-4df7-b2d7-5f0dbda5cbb3

import Mathlib.MeasureTheory.Function.L1Space.Integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

/-- The physical limit of integrable grid rewards inherits measurability,
then the common original envelope supplies integrability. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (J : ℕ → Ω → ℝ) (Z B : Ω → ℝ)
    (hInt : ∀ k, Integrable (J k) P)
    (hConv : ∀ᵐ ω ∂P, Tendsto (fun k => J k ω) atTop (𝓝 (Z ω)))
    (hBInt : Integrable B P)
    (hBound : ∀ᵐ ω ∂P, ‖Z ω‖ ≤ B ω) :
    Integrable Z P := by
  have hZMeas : AEStronglyMeasurable Z P := by
    exact aestronglyMeasurable_of_tendsto_ae atTop
      (fun k => (hInt k).aestronglyMeasurable) hConv
  apply Integrable.mono hBInt hZMeas
  filter_upwards [hBound] with ω hb
  exact hb.trans (le_abs_self (B ω))
