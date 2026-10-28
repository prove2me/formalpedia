-- Prove2me | solution 1 for AvramDividend.Classical.positive_gaussian_standing_and_unbounded_variation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T21:27:31.007912+00:00
-- url     : https://prove2.me/submissions/cbed295a-5d07-4d77-b716-765ea33374c8

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hσ : 0 < X.σ)
    (hI : Integrable (X.X 1) P) :
    X.Standing ∧ ¬ X.BoundedVariation := by
  have hBV : ¬ X.BoundedVariation := by
    intro hb
    exact (ne_of_gt hσ) hb.1
  refine ⟨⟨?_, hI, Or.inl hσ⟩, hBV⟩
  intro hmono
  exact hBV hmono.1
