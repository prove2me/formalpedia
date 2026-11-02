-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_05_actual_bounded_ruin_clocks_rightCont_stopping
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T08:57:35.433092+00:00
-- url     : https://prove2.me/submissions/c00e8b4b-7490-46f3-9277-eeca17dfba11

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Integer truncations of the actual controlled ruin are right-continuous stopping times. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) :
    ∀ n : ℕ, IsStoppingTime 𝓕.rightCont
      (fun ω : Ω => min (ruinTime X x D ω) (n : ℝ≥0∞)) := by
  intro n
  have hσ : IsStoppingTime 𝓕.rightCont (ruinTime X x D) :=
    ruinTime_stopping_rightCont_filtration X x D hD
  have hn : IsStoppingTime 𝓕.rightCont
      (fun _ : Ω => ((n : ℝ≥0) : ℝ≥0∞)) :=
    isStoppingTime_const 𝓕.rightCont (n : ℝ≥0)
  simpa using hσ.min hn
