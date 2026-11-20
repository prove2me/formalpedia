-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_closed_cash_antitone_clock_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T16:06:34.468445+00:00
-- url     : https://prove2.me/submissions/c850d875-a4b1-4775-ae2a-806f489c2b84

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (μ : Measure ℝ) (a : ℕ → ℝ) (s : ℝ)
    (ha : Antitone a)
    (hl : Tendsto a atTop (𝓝 s))
    (hfinite : ∃ n, μ (Iic (a n)) ≠ ∞) :
    Tendsto (fun n => μ (Iic (a n))) atTop
      (𝓝 (μ (Iic s))) := by
  have hb (n : ℕ) : s ≤ a n := by
    apply le_of_tendsto hl
    filter_upwards [Filter.eventually_ge_atTop n] with m hm
    exact ha hm
  have hset : (⋂ n, Iic (a n)) = Iic s := by
    ext x
    constructor
    · intro hx
      apply ge_of_tendsto hl
      exact Filter.Eventually.of_forall (fun n =>
        Set.mem_Iic.mp (Set.mem_iInter.mp hx n))
    · intro hx
      exact Set.mem_iInter.mpr (fun n =>
        Set.mem_Iic.mpr ((Set.mem_Iic.mp hx).trans (hb n)))
  have hanti : Antitone (fun n => (Iic (a n) : Set ℝ)) := by
    intro i j hij
    exact Iic_subset_Iic.mpr (ha hij)
  have hmeas (n : ℕ) : NullMeasurableSet (Iic (a n)) μ :=
    measurableSet_Iic.nullMeasurableSet
  simpa only [Function.comp_def, hset] using
    (tendsto_measure_iInter_atTop hmeas hanti hfinite)
