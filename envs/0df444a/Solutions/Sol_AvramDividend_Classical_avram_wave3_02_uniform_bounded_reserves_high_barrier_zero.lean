-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_02_uniform_bounded_reserves_high_barrier_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T20:53:00.855733+00:00
-- url     : https://prove2.me/submissions/05c1cdac-e0e7-4e0d-8a53-e6d6ca013cb9

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_positive_reserve_high_barrier_value_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_value_monotone_in_initial_capital

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- True expected discounted dividends vanish uniformly across any
bounded interval of nonnegative initial reserves as barrier tends to infinity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (R : ℝ) (hR : 0 ≤ R) :
    Tendsto (fun a : ℝ =>
      ⨆ x : ℝ, ⨆ (_ : 0 ≤ x ∧ x ≤ R),
        dividendValue X q x (barrierStrategy X x a))
      atTop (𝓝 (0 : ENNReal)) := by
  have hRplus : 0 < R + 1 := by linarith
  have hupper :=
    avram_wave3_02_positive_reserve_high_barrier_value_zero
      X hX q hq W hW (R + 1) hRplus
  have hle : ∀ᶠ a : ℝ in atTop,
      (⨆ x : ℝ, ⨆ (_ : 0 ≤ x ∧ x ≤ R),
        dividendValue X q x (barrierStrategy X x a)) ≤
      dividendValue X q (R + 1) (barrierStrategy X (R + 1) a) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with a ha
    refine iSup_le fun x => ?_
    refine iSup_le fun hx => ?_
    exact (avram_wave3_02_value_monotone_in_initial_capital
      X hX q hq W hW a ha)
        (Set.mem_Ici.mpr hx.1) (Set.mem_Ici.mpr (le_of_lt hRplus))
        (by linarith [hx.2])
  exact Filter.Tendsto.squeeze'
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ENNReal)) atTop (𝓝 0))
    hupper (Filter.Eventually.of_forall
      (fun a => (show (0 : ENNReal) ≤
        (⨆ x : ℝ, ⨆ (_ : 0 ≤ x ∧ x ≤ R),
          dividendValue X q x (barrierStrategy X x a)) from zero_le))) hle
