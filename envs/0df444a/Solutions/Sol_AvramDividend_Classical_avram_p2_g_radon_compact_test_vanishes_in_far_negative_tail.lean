-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_g_radon_compact_test_vanishes_in_far_negative_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T15:21:43.304572+00:00
-- url     : https://prove2.me/submissions/37ef3b42-a60f-451a-b9fb-c350ad5c4dd1

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Topology

/-- A compact negative-mark test vanishes beyond a finite negative
    threshold, giving the lower endpoint needed in exponential coordinates. -/
theorem solution
    (f : CompactlySupportedContinuousMap {x : ℝ // x < 0} ℝ) :
    ∃ R : ℝ, 0 < R ∧
      ∀ x : {x : ℝ // x < 0}, (x : ℝ) < -R → f x = 0 := by
  classical
  let K : Set {x : ℝ // x < 0} :=
    tsupport (fun x : {x : ℝ // x < 0} => f x)
  have hK : IsCompact K := f.hasCompactSupport
  have hmem (x : {x : ℝ // x < 0}) (hx : f x ≠ 0) : x ∈ K := by
    apply (subset_tsupport (fun y : {x : ℝ // x < 0} => f y))
    simpa [Function.mem_support] using hx
  by_cases hne : K.Nonempty
  · obtain ⟨x₀, hx₀, hmin⟩ :=
      hK.exists_isMinOn hne continuous_subtype_val.continuousOn
    refine ⟨-(x₀ : ℝ), neg_pos.mpr x₀.property, ?_⟩
    intro x hx
    by_contra hneq
    have hle : (x₀ : ℝ) ≤ (x : ℝ) := hmin (hmem x hneq)
    have hlt : (x : ℝ) < (x₀ : ℝ) := by simpa using hx
    exact (not_lt_of_ge hle) hlt
  · refine ⟨1, by norm_num, ?_⟩
    intro x hx
    by_contra hneq
    exact hne ⟨x, hmem x hneq⟩
