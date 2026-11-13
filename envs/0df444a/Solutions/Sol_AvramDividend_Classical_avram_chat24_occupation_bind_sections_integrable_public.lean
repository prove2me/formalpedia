-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat24_occupation_bind_sections_integrable_public
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T14:40:49.693948+00:00
-- url     : https://prove2.me/submissions/48c2c469-a893-45db-b9a6-21cb6433ba02

import Mathlib.MeasureTheory.Function.L1Space.Integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (P : Measure Ω) (K : Ω → Measure β) (hK : AEMeasurable K P)
    (H : β → ℝ) (hHm : Measurable H) (hHi : Integrable H (P.bind K)) :
    ∀ᵐ ω ∂P, Integrable H (K ω) := by
  have hinner : AEMeasurable (fun ω => ∫⁻ p, ‖H p‖ₑ ∂K ω) P :=
    (Measure.measurable_lintegral hHm.enorm).comp_aemeasurable hK
  have hfin : (∫⁻ ω, ∫⁻ p, ‖H p‖ₑ ∂K ω ∂P) < ⊤ := by
    rw [← Measure.lintegral_bind hK hHm.enorm.aemeasurable]
    exact hHi.2
  filter_upwards [ae_lt_top' hinner (ne_of_lt hfin)] with ω hω
  exact ⟨hHm.aestronglyMeasurable, hω⟩
end
