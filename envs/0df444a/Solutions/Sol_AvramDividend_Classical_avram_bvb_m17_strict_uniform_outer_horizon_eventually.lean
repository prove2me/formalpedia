-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_m17_strict_uniform_outer_horizon_eventually
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T17:53:16.77307+00:00
-- url     : https://prove2.me/submissions/74f41eb8-00e5-40d0-b1d8-9e338f7d85f8

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_avram_bva20_strict_inner_horizon_ruin_mask_eventual_equiv
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    (T r : ℝ) (hT : 0 < T) (hr : 0 < r) (hrT : r < T) :
    ∀ᶠ n in Filter.atTop,
      r < T * ((n : ℝ) + 1) / ((n : ℝ) + 2) := by
  have hdiff : 0 < T - r := sub_pos.mpr hrT
  filter_upwards [Filter.eventually_ge_atTop (T / (T - r))] with n hn
  have hnonneg : 0 ≤ n := le_trans (div_nonneg hT.le hdiff.le) hn
  have hden : 0 < n + 2 := by linarith
  apply (lt_div_iff₀ hden).2
  have hbound : T ≤ n * (T - r) := (div_le_iff₀ hdiff).1 hn
  nlinarith
