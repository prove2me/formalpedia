-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_reciprocal_cutoff_tsum_eq_full
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:33:28.403583+00:00
-- url     : https://prove2.me/submissions/509c8412-020f-4358-8bdb-0a192f00ff5d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_cutoff_tsum_monotone_convergence_core

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Reciprocal natural-number cutoffs exhaust an arbitrary ENNReal tsum,
including unbounded and uncountable index sets. -/
theorem solution
    {α : Type*} (f : α → ℝ≥0∞) :
    (⨆ n : ℕ, ∑' a : α,
      if (n : ℝ≥0∞)⁻¹ < f a then f a else 0) =
      ∑' a : α, f a := by
  apply avram_p3_a_bvdrift_cutoff_tsum_monotone_convergence_core f
    (fun n : ℕ => (n : ℝ≥0∞)⁻¹)
  · intro m n hmn
    exact ENNReal.inv_le_inv.mpr (by exact_mod_cast hmn)
  · intro a ha
    have hEv : ∀ᶠ n : ℕ in Filter.atTop, (n : ℝ≥0∞)⁻¹ < f a :=
      ENNReal.tendsto_inv_nat_nhds_zero.eventually (Iio_mem_nhds ha)
    exact hEv.exists