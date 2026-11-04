-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_bounded_residuals_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T07:53:29.076228+00:00
-- url     : https://prove2.me/submissions/ec1f3617-7a9d-41d7-b979-b9733f0e2ea3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- A truly bounded, a.e.-measurable stopped residual is L¹ under the original law. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (M G H : Ω → ℝ)
    (hMm : AEStronglyMeasurable M P)
    (hGm : AEStronglyMeasurable G P)
    (hHm : AEStronglyMeasurable H P)
    (BM BG BH : ℝ)
    (hMb : ∀ᵐ ω ∂P, ‖M ω‖ ≤ BM)
    (hGb : ∀ᵐ ω ∂P, ‖G ω‖ ≤ BG)
    (hHb : ∀ᵐ ω ∂P, ‖H ω‖ ≤ BH) :
    Integrable M P ∧ Integrable G P ∧ Integrable H P := by
  letI : IsProbabilityMeasure P := X.isProbability
  exact ⟨Integrable.of_bound hMm BM hMb,
    Integrable.of_bound hGm BG hGb,
    Integrable.of_bound hHm BH hHb⟩
