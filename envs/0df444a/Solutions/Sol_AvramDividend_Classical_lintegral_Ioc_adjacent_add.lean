-- Prove2me | solution 1 for AvramDividend.Classical.lintegral_Ioc_adjacent_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T21:37:36.325982+00:00
-- url     : https://prove2.me/submissions/9d720d4e-db4d-493a-ac24-5e29822d173c

import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Order.Interval.Set.LinearOrder

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal Classical
open AvramDividend.Classical

theorem solution
    (μ : Measure ℝ) (f : ℝ → ℝ≥0∞)
    (s t u : ℝ) (hst : s ≤ t) (htu : t ≤ u) :
    (∫⁻ r in Set.Ioc s u, f r ∂μ) =
      (∫⁻ r in Set.Ioc s t, f r ∂μ) +
      (∫⁻ r in Set.Ioc t u, f r ∂μ) := by
  have hd : Disjoint (Set.Ioc s t) (Set.Ioc t u) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact (not_lt_of_ge hx.2) hy.1
  rw [← Set.Ioc_union_Ioc_eq_Ioc hst htu]
  exact lintegral_union (μ := μ) (f := f)
    (A := Set.Ioc s t) (B := Set.Ioc t u) measurableSet_Ioc hd
