-- Prove2me | solution 1 for AvramDividend.Classical.zero_atom_free_stieltjes_reward_union
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T17:52:35.738051+00:00
-- url     : https://prove2.me/submissions/393f4aab-ccf2-465b-8591-9dbfd0260790

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
open MeasureTheory Set
open scoped ENNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Adjoining an initial null atom to a stopped Stieltjes payment set
does not alter its weighted lower integral. -/
theorem solution
    (μ : Measure ℝ) (f : ℝ → ℝ≥0∞) (s : Set ℝ)
    (hzero : μ {(0 : ℝ)} = 0) :
    (∫⁻ t in ({(0 : ℝ)} ∪ s), f t ∂μ) =
      (∫⁻ t in s, f t ∂μ) := by
  apply le_antisymm
  · calc
      (∫⁻ t in ({(0 : ℝ)} ∪ s), f t ∂μ) ≤
          (∫⁻ t in {(0 : ℝ)}, f t ∂μ) +
            (∫⁻ t in s, f t ∂μ) :=
        lintegral_union_le f {(0 : ℝ)} s
      _ = (∫⁻ t in s, f t ∂μ) := by
        rw [setLIntegral_measure_zero {(0 : ℝ)} f hzero, zero_add]
  · exact lintegral_mono_set (Set.subset_union_right)
