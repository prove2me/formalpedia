-- Prove2me | solution 1 for AvramDividend.Classical.dividendStrategy_rightCont_filtration
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T17:07:30.076303+00:00
-- url     : https://prove2.me/submissions/4a48f927-10e2-419e-b989-3c4d47df07d2

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) :
    IsDividendStrategy 𝓕.rightCont D := by
  refine ⟨hD.1, hD.2.1, hD.2.2.1, ?_⟩
  intro t
  exact (hD.2.2.2 t).mono (𝓕.le_rightCont t) le_rfl
