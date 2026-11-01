-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_05_source_all_cap_positive_jump_strip_bound_of_levy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T17:44:21.648525+00:00
-- url     : https://prove2.me/submissions/0f67e9ac-bfb8-4855-821f-8e1f0d18dfca

import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_levy_negative_mass_away_from_zero_finite
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_all_cap_positive_jump_part_exact
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The genuine source Levy measure has a finite ruin-crossing band;
the positive compensated jump kernel is uniformly bounded there. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (hx : (cstar W).toReal < x) :
    X.ν (Ioo (-1 : ℝ) (-x)) < ⊤ ∧
      ∀ y : ℝ, y < 0 →
        max 0 (SpectrallyNegativeLevy.generatorIntegrand (vcstar W) x y) ≤
          max 0 (1 - vcstar W x) := by
  have hx0 : 0 < x := lt_of_le_of_lt ENNReal.toReal_nonneg hx
  have hsubset : Ioo (-1 : ℝ) (-x) ⊆ Iic (-x) := by
    intro y hy
    exact le_of_lt hy.2
  constructor
  · exact lt_of_le_of_lt (measure_mono hsubset)
      (levy_negative_mass_away_from_zero_finite X x hx0)
  · intro y hy
    rw [avram_wave4_05_source_all_cap_positive_jump_part_exact
      X hX q hq W hW x hx y hy]
    by_cases hcross : y ∈ Ioo (-1 : ℝ) (-x)
    · rw [if_pos hcross]
      exact max_le_max_left 0 (by linarith [hcross.1])
    · rw [if_neg hcross]
      exact le_max_left _ _
