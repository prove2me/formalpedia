-- Prove2me | solution 1 for AvramDividend.Classical.avram_sweep17_cstar_inside_cap_bound_extends_all_capital
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T12:48:19.932345+00:00
-- url     : https://prove2.me/submissions/e2196db6-2d5d-4124-8918-8eaa97f2cbe8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_sweep17_cstar_boundary_to_above_cap

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (W : ℝ → ℝ)
    (hc : cstar W < ⊤)
    (hwc : 0 ≤ vcstar W (cstar W).toReal)
    (hInside :
      ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ cstar W →
        valueFunctionLe X q (cstar W) x ≤ ENNReal.ofReal (vcstar W x)) :
    ∀ x : ℝ, 0 ≤ x →
      valueFunctionLe X q (cstar W) x ≤ ENNReal.ofReal (vcstar W x) := by
  have hctop : cstar W ≠ ⊤ := ne_of_lt hc
  have hceq : ENNReal.ofReal (cstar W).toReal = cstar W :=
    ENNReal.ofReal_toReal hctop
  have hc0 : 0 ≤ (cstar W).toReal := ENNReal.toReal_nonneg
  have hBoundary :
      valueFunctionLe X q (cstar W) (cstar W).toReal ≤
        ENNReal.ofReal (vcstar W (cstar W).toReal) :=
    hInside (cstar W).toReal hc0 (le_of_eq hceq)
  intro x hx
  by_cases hxcap : ENNReal.ofReal x ≤ cstar W
  · exact hInside x hx hxcap
  · have hgt : cstar W < ENNReal.ofReal x := lt_of_not_ge hxcap
    have hcx : (cstar W).toReal < x :=
      (ENNReal.lt_ofReal_iff_toReal_lt hctop).mp hgt
    exact avram_sweep17_cstar_boundary_to_above_cap
      X q W hc hwc hBoundary x hcx.le
