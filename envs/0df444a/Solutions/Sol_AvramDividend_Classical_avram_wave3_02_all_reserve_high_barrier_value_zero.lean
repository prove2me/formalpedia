-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_02_all_reserve_high_barrier_value_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T20:47:56.336979+00:00
-- url     : https://prove2.me/submissions/e57365d4-3f67-4f82-a3df-bdf3a785f400

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

/-- For any nonnegative initial capital, including zero, the true
expected discounted dividend value vanishes as the barrier tends to infinity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (hx : 0 ≤ x) :
    Tendsto (fun a : ℝ => dividendValue X q x (barrierStrategy X x a))
      atTop (𝓝 (0 : ENNReal)) := by
  have hxplus : 0 < x + 1 := by linarith
  have hupper :=
    avram_wave3_02_positive_reserve_high_barrier_value_zero
      X hX q hq W hW (x + 1) hxplus
  have hmono : ∀ᶠ a : ℝ in atTop,
      dividendValue X q x (barrierStrategy X x a) ≤
        dividendValue X q (x + 1) (barrierStrategy X (x + 1) a) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with a ha
    exact (avram_wave3_02_value_monotone_in_initial_capital
      X hX q hq W hW a ha)
        (Set.mem_Ici.mpr hx) (Set.mem_Ici.mpr (le_of_lt hxplus))
        (by linarith)
  exact Filter.Tendsto.squeeze'
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ENNReal)) atTop (𝓝 0))
    hupper (Filter.Eventually.of_forall
      (fun a => (show (0 : ENNReal) ≤
        dividendValue X q x (barrierStrategy X x a) from zero_le))) hmono
