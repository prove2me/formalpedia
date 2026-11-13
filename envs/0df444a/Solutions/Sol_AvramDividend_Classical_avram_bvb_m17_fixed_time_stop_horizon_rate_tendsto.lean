-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_m17_fixed_time_stop_horizon_rate_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T17:47:04.933282+00:00
-- url     : https://prove2.me/submissions/b981078e-3bbe-4a1e-b101-758dd7590f85

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bva20_strict_inner_horizon_ruin_mask_eventual_equiv
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    (T r : ℝ) (hT : 0 < T) (hr : 0 < r) (hrT : r < T)
    (τ : ℝ≥0∞) (hτ : ENNReal.ofReal r ≠ τ)
    (active : Prop) [Decidable active] (rate : ℝ) :
    Filter.Tendsto
      (fun n : ℕ =>
        if (0 < r ∧ r < T - T / ((n : ℝ) + 2) ∧
            ENNReal.ofReal r ≤ τ) ∧ active then rate else 0)
      Filter.atTop
      (𝓝 (if (0 < r ∧ ENNReal.ofReal r < τ) ∧ active
        then rate else 0)) := by
  have he := avram_bva20_strict_inner_horizon_ruin_mask_eventual_equiv
    T hT τ r hr hrT hτ
  apply tendsto_const_nhds.congr'
  filter_upwards [he] with n hn
  have heq : ((0 < r ∧ r < T - T / ((n : ℝ) + 2) ∧
      ENNReal.ofReal r ≤ τ) ∧ active) ↔
      ((0 < r ∧ ENNReal.ofReal r < τ) ∧ active) :=
    and_congr hn Iff.rfl
  by_cases h : ((0 < r ∧ r < T - T / ((n : ℝ) + 2) ∧
      ENNReal.ofReal r ≤ τ) ∧ active)
  · have hg : (0 < r ∧ ENNReal.ofReal r < τ) ∧ active :=
      heq.mp h
    simp [h, hg]
  · have hg : ¬ ((0 < r ∧ ENNReal.ofReal r < τ) ∧ active) :=
      fun k => h (heq.mpr k)
    simp [h, hg]
