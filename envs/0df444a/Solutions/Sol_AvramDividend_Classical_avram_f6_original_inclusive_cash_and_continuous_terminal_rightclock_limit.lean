-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_inclusive_cash_and_continuous_terminal_rightclock_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T17:30:57.728887+00:00
-- url     : https://prove2.me/submissions/d32b6501-cd24-40ac-bea7-0cc9d76e7522

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
    (ha : Antitone a) (hl : Tendsto a atTop (𝓝 s))
    (hfinite : ∃ n, μ (Iic (a n)) ≠ ∞)
    (f : ℝ → ℝ)
    (hf : ContinuousWithinAt f (Ici s) s) :
    Tendsto (fun n => f (a n) + (μ (Iic (a n))).toReal)
      atTop (𝓝 (f s + (μ (Iic s)).toReal)) := by
  obtain ⟨i, hi⟩ := hfinite
  have hsle (n : ℕ) : s ≤ a n := by
    apply le_of_tendsto hl
    filter_upwards [Filter.eventually_ge_atTop n] with j hj
    exact ha hj
  have hwithin : Tendsto a atTop (𝓝[Ici s] s) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hl, Filter.Eventually.of_forall (fun n => hsle n)⟩
  have hμle : μ (Iic s) ≤ μ (Iic (a i)) :=
    measure_mono (Iic_subset_Iic.mpr (hsle i))
  have hlimfinite : μ (Iic s) ≠ ∞ := ne_top_of_le_ne_top hi hμle
  have hcash := (ENNReal.tendsto_toReal hlimfinite).comp
    (avram_f6_original_closed_cash_antitone_clock_limit
      μ a s ha hl ⟨i, hi⟩)
  simpa only [Function.comp_def] using (hf.tendsto.comp hwithin).add hcash
