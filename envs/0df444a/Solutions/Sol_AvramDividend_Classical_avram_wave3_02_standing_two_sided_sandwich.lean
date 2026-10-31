-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_02_standing_two_sided_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T07:41:54.425445+00:00
-- url     : https://prove2.me/submissions/f355b33d-b98d-404c-bca3-9511cda9afbf

import Mathlib.Topology.Order.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_standing_left_step_lower
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_standing_all_right_step_upper
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

/-- Unconditional original reflected-regulator renewal sandwich at small
positive record meshes, independent of W differentiability and scale C1. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal (ε * W (a - ε) / (W a - W (a - ε))) ≤
        barrierSupValue X a q ∧
      barrierSupValue X a q ≤
        ENNReal.ofReal (ε * W (a + ε) / (W (a + ε) - W a)) := by
  have hpositive : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := by
    change Set.Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ)
    exact self_mem_nhdsWithin
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < a :=
    (eventually_lt_nhds ha).filter_mono nhdsWithin_le_nhds
  filter_upwards [hpositive, hsmall] with ε hε hεa
  constructor
  · exact avram_wave3_02_standing_left_step_lower
      X hX q hq W hW a ε ha hε hεa
  · exact avram_wave3_02_standing_all_right_step_upper
      X hX q hq W hW a ha ε hε
