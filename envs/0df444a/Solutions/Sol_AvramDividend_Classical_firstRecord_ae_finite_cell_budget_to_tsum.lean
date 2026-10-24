-- Prove2me | solution 1 for AvramDividend.Classical.firstRecord_ae_finite_cell_budget_to_tsum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T22:26:38.178996+00:00
-- url     : https://prove2.me/submissions/0e71ac29-307d-4df8-bb44-aaa529637628

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal BigOperators

/-! Countably many a.e. finite-grid estimates imply an a.e. bound on the infinite reward. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (f : ℕ → Ω → ℝ≥0∞) (C : Ω → ℝ≥0∞)
    (hfinite : ∀ N : ℕ, ∀ᵐ ω ∂P,
      (∑ n ∈ Finset.range N, f n ω) ≤ C ω) :
    ∀ᵐ ω ∂P, (∑' n, f n ω) ≤ C ω := by
  have hh : ∀ᵐ ω ∂P, ∀ N : ℕ,
      (∑ n ∈ Finset.range N, f n ω) ≤ C ω :=
    (MeasureTheory.ae_all_iff).2 hfinite
  refine hh.mono ?_
  intro ω hω
  rw [ENNReal.tsum_eq_iSup_nat]
  exact iSup_le hω
