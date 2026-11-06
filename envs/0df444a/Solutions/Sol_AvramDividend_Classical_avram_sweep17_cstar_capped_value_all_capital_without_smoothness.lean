-- Prove2me | solution 1 for AvramDividend.Classical.avram_sweep17_cstar_capped_value_all_capital_without_smoothness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T13:19:13.326565+00:00
-- url     : https://prove2.me/submissions/aea6a444-434d-41a8-8ffe-7d94b65c4db7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_sweep17_vcstar_nonnegative_without_smoothness
import Theorems.Thm_AvramDividend_Classical_avram_sweep17_cstar_inside_cap_bound_extends_all_capital

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤)
    (hInside :
      ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ cstar W →
        valueFunctionLe X q (cstar W) x ≤ ENNReal.ofReal (vcstar W x)) :
    ∀ x : ℝ, 0 ≤ x →
      valueFunctionLe X q (cstar W) x ≤ ENNReal.ofReal (vcstar W x) := by
  have hwc : 0 ≤ vcstar W (cstar W).toReal :=
    avram_sweep17_vcstar_nonnegative_without_smoothness
      X hX q hq W hW hc (cstar W).toReal ENNReal.toReal_nonneg
  exact avram_sweep17_cstar_inside_cap_bound_extends_all_capital
    X q W hc hwc hInside

