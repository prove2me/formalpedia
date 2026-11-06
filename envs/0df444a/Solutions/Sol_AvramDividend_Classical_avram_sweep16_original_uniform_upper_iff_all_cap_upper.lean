-- Prove2me | solution 1 for AvramDividend.Classical.avram_sweep16_original_uniform_upper_iff_all_cap_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:26:16.205005+00:00
-- url     : https://prove2.me/submissions/c8fce63f-51c0-47ee-8c06-4a16ee52a7cc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_unrestricted_upper_iff_all_cap_uppers

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (w : ℝ → ℝ) :
    (∀ x : ℝ, 0 ≤ x →
      valueFunction X q x ≤ ENNReal.ofReal (w x)) ↔
    (∀ x : ℝ, 0 ≤ x → ∀ C : ℝ≥0∞,
      valueFunctionLe X q C x ≤ ENNReal.ofReal (w x)) := by
  constructor
  · intro hUpper x hx C
    exact (avram_sweep16_unrestricted_upper_iff_all_cap_uppers
      X q x (ENNReal.ofReal (w x))).2 (hUpper x hx) C
  · intro hAll x hx
    exact (avram_sweep16_unrestricted_upper_iff_all_cap_uppers
      X q x (ENNReal.ofReal (w x))).1 (fun C => hAll x hx C)
