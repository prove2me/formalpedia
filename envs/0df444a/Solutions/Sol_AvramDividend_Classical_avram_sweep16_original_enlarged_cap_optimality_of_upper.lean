-- Prove2me | solution 1 for AvramDividend.Classical.avram_sweep16_original_enlarged_cap_optimality_of_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:07:17.714267+00:00
-- url     : https://prove2.me/submissions/33db6c2c-341b-486a-b333-13431644d6d1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_enlarged_cap_barrier_lower

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (C : ℝ≥0∞) (hCap : cstar W ≤ C)
    (hUpper : ∀ x : ℝ, 0 ≤ x →
      valueFunctionLe X q C x ≤ ENNReal.ofReal (vcstar W x)) :
    ∀ x : ℝ, 0 ≤ x →
      valueFunctionLe X q C x = ENNReal.ofReal (vcstar W x) := by
  intro x hx
  exact le_antisymm (hUpper x hx)
    (avram_sweep16_original_enlarged_cap_barrier_lower
      X hX q hq W hW C hCap x hx)
