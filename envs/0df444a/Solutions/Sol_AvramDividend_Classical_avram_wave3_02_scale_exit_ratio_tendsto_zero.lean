-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_02_scale_exit_ratio_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T20:57:52.119346+00:00
-- url     : https://prove2.me/submissions/354a5569-949b-470e-bd5b-f377a5ab2fbc

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Algebra.Order.Field
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_scale_tendsto_atTop

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- For any fixed starting capital, the original q-scale two-sided
first-upcrossing quotient tends to zero at an infinite upper barrier. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) :
    Tendsto (fun a : ℝ => W x / W a) atTop (𝓝 (0 : ℝ)) := by
  exact Filter.Tendsto.div_atTop tendsto_const_nhds
    (avram_wave3_02_scale_tendsto_atTop X hX q hq W hW)
