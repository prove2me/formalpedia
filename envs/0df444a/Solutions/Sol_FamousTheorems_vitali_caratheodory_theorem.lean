-- Prove2me | solution 1 for FamousTheorems.vitali_caratheodory_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:42:19.404363+00:00
-- url     : https://prove2.me/submissions/11df94a8-0bf4-425d-997f-6e79a1d629ee

import Mathlib

open MeasureTheory

theorem solution {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α] {μ : Measure α}
    [μ.WeaklyRegular] [SigmaFinite μ] (f : α → ℝ) (hf : Integrable f μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : α → EReal, (∀ x, (f x : EReal) < g x) ∧ LowerSemicontinuous g ∧
      Integrable (fun x => (g x).toReal) μ ∧ (∀ᵐ x ∂μ, g x < ⊤) ∧
        ∫ x, (g x).toReal ∂μ < ∫ x, f x ∂μ + ε :=
  exists_lt_lowerSemicontinuous_integral_lt f hf hε
