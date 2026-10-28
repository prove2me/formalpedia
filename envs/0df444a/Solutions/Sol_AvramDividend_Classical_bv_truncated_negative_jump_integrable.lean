-- Prove2me | solution 1 for AvramDividend.Classical.bv_truncated_negative_jump_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:22:32.378848+00:00
-- url     : https://prove2.me/submissions/a0249d44-b436-40eb-ae24-b5dacd049dde

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_boundedVariation_smallJump_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The BV finite first moment supplies the generator's truncated jump integrability. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hbv : X.BoundedVariation) :
    IntegrableOn
      (fun y : ℝ =>
        y * (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y)
      (Iio (0 : ℝ)) X.ν := by
  have hglobal : Integrable
      ((Ioo (-1 : ℝ) 0).indicator (fun y : ℝ => y)) X.ν :=
    (boundedVariation_smallJump_integrable X hbv).integrable_indicator measurableSet_Ioo
  have heq :
      ∀ y ∈ Iio (0 : ℝ),
        (Ioo (-1 : ℝ) 0).indicator (fun z : ℝ => z) y =
          y * (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y := by
    intro y hy
    have hyneg : y < 0 := hy
    by_cases hsmall : -1 < y
    · have hleft : y ∈ Ioo (-1 : ℝ) 0 := ⟨hsmall, hyneg⟩
      have hright : y ∈ Ioo (-1 : ℝ) 1 := ⟨hsmall, by linarith⟩
      simp [Set.indicator_of_mem hleft, Set.indicator_of_mem hright]
    · have hleft : y ∉ Ioo (-1 : ℝ) 0 := by
        intro h
        exact hsmall h.1
      have hright : y ∉ Ioo (-1 : ℝ) 1 := by
        intro h
        exact hsmall h.1
      simp [Set.indicator_of_notMem hleft, Set.indicator_of_notMem hright]
  exact hglobal.integrableOn.congr_fun heq measurableSet_Iio
