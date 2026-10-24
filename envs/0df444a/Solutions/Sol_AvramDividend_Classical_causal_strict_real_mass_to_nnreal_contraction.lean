-- Prove2me | solution 1 for AvramDividend.Classical.causal_strict_real_mass_to_nnreal_contraction
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T07:12:41.032015+00:00
-- url     : https://prove2.me/submissions/17695779-c0ec-403c-999b-3599c42cf27c

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Tactic.FieldSimp
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
open scoped NNReal ENNReal

/-- An admissible weighted kernel mass supplies a strict contraction ratio. -/
theorem solution (a m : ℝ)
    (ha : 0 < a) (hm : 0 ≤ m) (hsmall : m < a) :
    ∃ c : NNReal, c < 1 ∧ (c : ℝ) * a = m := by
  let c : NNReal := ⟨m / a, div_nonneg hm ha.le⟩
  refine ⟨c, ?_, ?_⟩
  · change m / a < 1
    apply (div_lt_iff₀ ha).2
    simpa only [one_mul] using hsmall
  · change m / a * a = m
    field_simp [ne_of_gt ha]
