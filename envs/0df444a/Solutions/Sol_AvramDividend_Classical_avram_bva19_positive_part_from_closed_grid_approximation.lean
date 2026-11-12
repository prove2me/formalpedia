-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva19_positive_part_from_closed_grid_approximation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T18:02:17.585291+00:00
-- url     : https://prove2.me/submissions/7e546e71-942e-4d5f-9b02-f3a786ba8aa8

import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Order.Filter.Pointwise
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    (K A J : ℕ → ℝ)
    (hApprox : Tendsto (fun n => K n - A n) atTop (𝓝 (0 : ℝ)))
    (hSigned : ∀ n, A n ≤ J n) :
    Tendsto (fun n => max (K n - J n) 0) atTop (𝓝 (0 : ℝ)) := by
  have hUpper (n : ℕ) : max (K n - J n) 0 ≤ |K n - A n| := by
    have hReal : K n - J n ≤ K n - A n := sub_le_sub_left (hSigned n) _
    have hAbs : K n - A n ≤ |K n - A n| := le_abs_self _
    exact max_le (hReal.trans hAbs) (abs_nonneg _)
  have hMax : Tendsto (fun n => max (K n - A n) (0 : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [max_self] using
      hApprox.max (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  have hBound (n : ℕ) : max (K n - J n) 0 ≤ max (K n - A n) 0 :=
    max_le_max_right 0 (sub_le_sub_left (hSigned n) _)
  exact squeeze_zero (fun n => le_max_right _ _) hBound hMax
