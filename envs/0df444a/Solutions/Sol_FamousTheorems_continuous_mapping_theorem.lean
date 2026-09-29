-- Prove2me | solution 1 for FamousTheorems.continuous_mapping_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T18:23:54.472139+00:00
-- url     : https://prove2.me/submissions/ba997ed2-cd18-4647-ad9b-ca724cf19087

import Mathlib

theorem solution {ι E Ω' F : Type*} {Ω : ι → Type*} {m : ∀ i, MeasurableSpace (Ω i)} {μ : ∀ i, MeasureTheory.Measure (Ω i)}
    [∀ i, MeasureTheory.IsProbabilityMeasure (μ i)] {m' : MeasurableSpace Ω'} {μ' : MeasureTheory.Measure Ω'}
    [MeasureTheory.IsProbabilityMeasure μ'] {mE : MeasurableSpace E} {X : ∀ i, Ω i → E} {Z : Ω' → E}
    {l : Filter ι} [TopologicalSpace E] [OpensMeasurableSpace E] [TopologicalSpace F] [MeasurableSpace F]
    [BorelSpace F] {g : E → F} (hg : Continuous g) (h : MeasureTheory.TendstoInDistribution X l Z μ μ') :
    MeasureTheory.TendstoInDistribution (fun n => g ∘ X n) l (g ∘ Z) μ μ' :=
  h.continuous_comp hg
