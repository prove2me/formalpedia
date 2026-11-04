-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_g_radon_compact_test_separated_from_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T14:52:43.954618+00:00
-- url     : https://prove2.me/submissions/4cd11ee8-3c2f-447c-8686-ac3834a2d576

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Topology

/-- Compact support in the open negative half-line stays a positive
    distance from its missing boundary point zero. -/
theorem solution
    (f : CompactlySupportedContinuousMap {x : ℝ // x < 0} ℝ) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ x : {x : ℝ // x < 0}, -ε < (x : ℝ) → f x = 0 := by
  classical
  let K : Set {x : ℝ // x < 0} :=
    tsupport (fun x : {x : ℝ // x < 0} => f x)
  have hK : IsCompact K := f.hasCompactSupport
  have hmem (x : {x : ℝ // x < 0}) (hx : f x ≠ 0) : x ∈ K := by
    apply (subset_tsupport (fun y : {x : ℝ // x < 0} => f y))
    simpa [Function.mem_support] using hx
  by_cases hne : K.Nonempty
  · obtain ⟨x₀, hx₀, hmax⟩ :=
      hK.exists_isMaxOn hne continuous_subtype_val.continuousOn
    refine ⟨-(x₀ : ℝ), neg_pos.mpr x₀.property, ?_⟩
    intro x hx
    by_contra hneq
    have hle : (x : ℝ) ≤ (x₀ : ℝ) := hmax (hmem x hneq)
    have hlt : (x₀ : ℝ) < (x : ℝ) := by simpa using hx
    exact (not_lt_of_ge hle) hlt
  · refine ⟨1, by norm_num, ?_⟩
    intro x hx
    by_contra hneq
    exact hne ⟨x, hmem x hneq⟩
