-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_m_uniqueness_clamped_unit_nnreal_bounded_continuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T16:53:05.101424+00:00
-- url     : https://prove2.me/submissions/2db3961d-4763-4de6-8702-754fe2313564

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Topology BoundedContinuousFunction
open scoped NNReal ENNReal

/-- The identity on [0,1] has a globally bounded continuous NNReal-valued
extension which agrees with the ENNReal `ofReal` embedding on that interval. -/
theorem solution :
    ∃ f : ℝ →ᵇ ℝ≥0,
      (∀ z : ℝ, f z ≤ 1) ∧
      ∀ z : ℝ, z ∈ Set.Icc (0 : ℝ) 1 →
        (f z : ℝ≥0∞) = ENNReal.ofReal z := by
  let g : ℝ → ℝ≥0 := fun z => Real.toNNReal (max (0 : ℝ) (min 1 z))
  have hclamp : Continuous (fun z : ℝ => max (0 : ℝ) (min 1 z)) :=
    continuous_const.max (continuous_const.min continuous_id)
  have hgc : Continuous g := continuous_real_toNNReal.comp hclamp
  have hgle (z : ℝ) : g z ≤ 1 := by
    have hreal : max (0 : ℝ) (min 1 z) ≤ 1 :=
      max_le (by norm_num) (min_le_left _ _)
    simpa [g] using Real.toNNReal_mono hreal
  have hb : Bornology.IsBounded (Set.range g) :=
    isCompact_Icc.isBounded.subset (by
      rintro _ ⟨z, rfl⟩
      exact ⟨zero_le, hgle z⟩)
  let f : ℝ →ᵇ ℝ≥0 :=
    ⟨⟨g, hgc⟩, Metric.isBounded_range_iff.mp hb⟩
  refine ⟨f, (fun z => hgle z), ?_⟩
  intro z hz
  change (g z : ℝ≥0∞) = ENNReal.ofReal z
  have hc : max (0 : ℝ) (min 1 z) = z := by
    rw [min_eq_right hz.2, max_eq_right hz.1]
  simp only [g, hc]
  rw [Real.toNNReal_of_nonneg hz.1, ENNReal.ofReal_eq_coe_nnreal hz.1]
