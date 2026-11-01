-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_05_source_zero_landing_compensated_kernel_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T22:45:45.558388+00:00
-- url     : https://prove2.me/submissions/9d917218-e71f-41e3-be8d-e3e821164b2b

import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_signed_jump_bound
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The actual compensated generator kernel of a jump landing exactly at
zero is nonpositive above any finite optimal barrier, including barrier zero.
No atomlessness or first-moment assumption is required. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (hx : (cstar W).toReal < x) :
    SpectrallyNegativeLevy.generatorIntegrand (vcstar W) x (-x) ≤ 0 := by
  have hx0 : 0 < x := lt_of_le_of_lt ENNReal.toReal_nonneg hx
  have hyneg : -x < 0 := neg_lt_zero.mpr hx0
  have hS : -x ∉ Ioo (-1 : ℝ) (-x) := by
    intro hy
    exact (lt_irrefl (-x)) hy.2
  have hL : -x ∉ Iic (-1 : ℝ) ∩ Iio (-x) := by
    intro hy
    exact (lt_irrefl (-x)) hy.2
  have hbound := avram_wave4_05_source_signed_jump_bound
    X hX q hq W hW x hx (-x) hyneg
  simpa [hS, hL] using hbound
