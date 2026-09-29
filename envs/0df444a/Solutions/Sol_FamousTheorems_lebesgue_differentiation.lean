-- Prove2me | solution 1 for FamousTheorems.lebesgue_differentiation
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T09:19:53.213523+00:00
-- url     : https://prove2.me/submissions/6c63b5b5-4e57-45ac-90fd-15989f5037a5

import Mathlib

open MeasureTheory

theorem solution {α : Type*} [PseudoMetricSpace α] {m0 : MeasurableSpace α} {μ : Measure α} (v : VitaliFamily μ)
    [SecondCountableTopology α] [BorelSpace α] [IsLocallyFiniteMeasure μ] {f : α → ENNReal}
    (hf : AEMeasurable f μ) (h'f : ∫⁻ y, f y ∂μ ≠ ⊤) :
    ∀ᵐ x ∂μ, Filter.Tendsto (fun a => (∫⁻ y in a, f y ∂μ) / μ a) (v.filterAt x) (nhds (f x)) :=
  v.ae_tendsto_lintegral_div hf h'f
