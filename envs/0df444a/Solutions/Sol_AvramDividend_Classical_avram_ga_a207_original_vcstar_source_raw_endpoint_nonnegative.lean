-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a207_original_vcstar_source_raw_endpoint_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:34:30.304205+00:00
-- url     : https://prove2.me/submissions/93ba97f1-8baf-4177-af3b-f49fda298ef5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy


import Theorems.Thm_AvramDividend_Classical_avram_sweep17_vcstar_nonnegative_without_smoothness
import Theorems.Thm_AvramDividend_Classical_vcstar_eq_zero_of_neg
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical


/-- The exact original Gaussian raw source observation, evaluated before
its dividend payment, is nonnegative for the actual candidate barrier value.
The negative-reserve extension is handled by the published zero lemma. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hc : cstar W < ⊤)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (s t : ℝ≥0) (ω : Ω) :
    0 ≤ vcstar W (x + X.X t ω - rightLimit D s ω) := by
  let y : ℝ := x + X.X t ω - rightLimit D s ω
  change 0 ≤ vcstar W y
  by_cases hy : 0 ≤ y
  · exact avram_sweep17_vcstar_nonnegative_without_smoothness
      X hX q hq W hW hc y hy
  · have hneg : y < 0 := lt_of_not_ge hy
    rw [vcstar_eq_zero_of_neg W y hneg]
