-- Prove2me | solution 1 for AvramDividend.Classical.avram_sweep16_all_enlarged_caps_optimal_of_global_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:10:58.304243+00:00
-- url     : https://prove2.me/submissions/29dc5bdc-b914-4d41-9eda-2cdbc417e108

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_enlarged_cap_barrier_lower
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_capped_value_le_unrestricted_value

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
    (hUpper : ∀ x : ℝ, 0 ≤ x →
      valueFunction X q x ≤ ENNReal.ofReal (vcstar W x)) :
    ∀ C : ℝ≥0∞, cstar W ≤ C →
      ∀ x : ℝ, 0 ≤ x →
        valueFunctionLe X q C x = ENNReal.ofReal (vcstar W x) := by
  intro C hCap x hx
  apply le_antisymm
  · exact (avram_sweep16_original_capped_value_le_unrestricted_value X q x C).trans
      (hUpper x hx)
  · exact avram_sweep16_original_enlarged_cap_barrier_lower X hX q hq W hW C hCap x hx
