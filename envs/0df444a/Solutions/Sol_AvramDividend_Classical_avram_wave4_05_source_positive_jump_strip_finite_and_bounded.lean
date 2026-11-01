-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_05_source_positive_jump_strip_finite_and_bounded
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T16:58:14.498822+00:00
-- url     : https://prove2.me/submissions/92d5780a-aa48-45a0-aad8-49f9da2d8036

import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_negative_jump_truncation_measure_finite
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_positive_jump_part_exact
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The sole possible positive compensated jump band is finite under the
genuine Levy second-moment bound, with a uniform pointwise kernel bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hpos : 0 < (cstar W).toReal)
    (x : ℝ) (hx : (cstar W).toReal < x)
    (hνint : ∫⁻ y, ENNReal.ofReal (min 1 (y ^ 2)) ∂X.ν < ⊤) :
    X.ν (Ioo (-1 : ℝ) (-x)) < ⊤ ∧
      ∀ y : ℝ, y < 0 →
        max 0 (SpectrallyNegativeLevy.generatorIntegrand (vcstar W) x y) ≤
          max 0 (1 - vcstar W x) := by
  have hx0 : 0 < x := lt_trans hpos hx
  have hsubset : Ioo (-1 : ℝ) (-x) ⊆ Iic (-x) := by
    intro y hy
    exact le_of_lt hy.2
  constructor
  · exact lt_of_le_of_lt (measure_mono hsubset)
      (negative_jump_truncation_measure_finite X.ν hνint x hx0)
  · intro y hy
    rw [avram_wave4_05_source_positive_jump_part_exact
      X hX q hq W hW hpos x hx y hy]
    by_cases hcross : y ∈ Ioo (-1 : ℝ) (-x)
    · rw [if_pos hcross]
      exact max_le_max_left 0 (by linarith [hcross.1])
    · rw [if_neg hcross]
      exact le_max_left _ _
