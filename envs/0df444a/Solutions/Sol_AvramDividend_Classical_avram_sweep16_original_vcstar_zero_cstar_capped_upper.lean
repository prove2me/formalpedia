-- Prove2me | solution 1 for AvramDividend.Classical.avram_sweep16_original_vcstar_zero_cstar_capped_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T12:24:59.933+00:00
-- url     : https://prove2.me/submissions/5f551dca-41a6-44a6-ab0f-90590b0e4119

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_zero_cap_value_at_zero_upper_bound
import Theorems.Thm_AvramDividend_Classical_barrier_zero_boundary_value_nonneg
import Theorems.Thm_AvramDividend_Classical_zero_cap_value_upper_bound_of_zero_bound

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
    (hc0 : cstar W = 0) :
    ∀ x : ℝ, 0 ≤ x →
      valueFunctionLe X q (cstar W) x ≤ ENNReal.ofReal (vcstar W x) := by
  intro x hx
  have hboundary :=
    zero_cap_value_at_zero_upper_bound X hX q hq W hW
  have hval := (barrier_zero_boundary_value_nonneg X hX q hq W hW).1
  have hAll := zero_cap_value_upper_bound_of_zero_bound X q W hboundary hval x hx
  simpa [vcstar, hc0] using hAll
