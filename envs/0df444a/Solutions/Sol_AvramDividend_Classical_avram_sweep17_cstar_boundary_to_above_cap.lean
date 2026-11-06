-- Prove2me | solution 1 for AvramDividend.Classical.avram_sweep17_cstar_boundary_to_above_cap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T12:43:29.90527+00:00
-- url     : https://prove2.me/submissions/ab23330f-3870-4de1-afad-98555046a355

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_capped_boundary_bound_extends_above_cap

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (W : ℝ → ℝ)
    (hc : cstar W < ⊤)
    (hwc : 0 ≤ vcstar W (cstar W).toReal)
    (hBoundary :
      valueFunctionLe X q (cstar W) (cstar W).toReal ≤
        ENNReal.ofReal (vcstar W (cstar W).toReal)) :
    ∀ x : ℝ, (cstar W).toReal ≤ x →
      valueFunctionLe X q (cstar W) x ≤ ENNReal.ofReal (vcstar W x) := by
  have hc0 : 0 ≤ (cstar W).toReal := ENNReal.toReal_nonneg
  have hof : ENNReal.ofReal (cstar W).toReal = cstar W :=
    ENNReal.ofReal_toReal (ne_of_lt hc)
  have hAffine : ∀ x : ℝ, (cstar W).toReal < x →
      vcstar W x = x - (cstar W).toReal + vcstar W (cstar W).toReal := by
    intro x hcx
    have hx : 0 ≤ x := hc0.trans hcx.le
    unfold vcstar barrierValue
    rw [if_neg (not_lt.mpr hx), if_neg (not_le.mpr hcx)]
    rw [if_neg (not_lt.mpr hc0), if_pos le_rfl]
  have hBoundary' :
      valueFunctionLe X q (ENNReal.ofReal (cstar W).toReal) (cstar W).toReal ≤
        ENNReal.ofReal (vcstar W (cstar W).toReal) := by
    simpa only [hof] using hBoundary
  intro x hx
  have hAbove :=
    avram_sweep16_original_capped_boundary_bound_extends_above_cap
      X q (cstar W).toReal hc0 (vcstar W) hwc hBoundary' hAffine x hx
  simpa only [hof] using hAbove
