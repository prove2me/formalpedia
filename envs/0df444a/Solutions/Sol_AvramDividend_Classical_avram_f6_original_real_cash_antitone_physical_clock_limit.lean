-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_real_cash_antitone_physical_clock_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T17:20:27.102619+00:00
-- url     : https://prove2.me/submissions/8e8834d4-b451-4433-8bdc-3b1c8563536b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_closed_cash_antitone_clock_limit
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
    Tendsto (fun n => (μ (Iic (a n))).toReal) atTop
      (𝓝 ((μ (Iic s)).toReal)) := by
  obtain ⟨i, hi⟩ := hfinite
  have hsle : s ≤ a i := by
    apply le_of_tendsto hl
    filter_upwards [Filter.eventually_ge_atTop i] with j hj
    exact ha hj
  have hμle : μ (Iic s) ≤ μ (Iic (a i)) :=
    measure_mono (Iic_subset_Iic.mpr hsle)
  have hlimfinite : μ (Iic s) ≠ ∞ := ne_top_of_le_ne_top hi hμle
  exact (ENNReal.tendsto_toReal hlimfinite).comp
    (avram_f6_original_closed_cash_antitone_clock_limit
      μ a s ha hl ⟨i, hi⟩)
