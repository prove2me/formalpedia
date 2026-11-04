-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_original_raw_real_jump_total_endpoint_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T15:50:21.232757+00:00
-- url     : https://prove2.me/submissions/d941c960-1d0e-46b8-8a60-b2563c24d093

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_interval_raw_negative_jump_real_tsum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The genuine original BV signed real jump series splits into the
positive-time endpoint atom and the strict-past real left-jump series. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t →
      (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0) =
      (Function.leftLim (fun z : ℝ≥0 => X.X z ω) t - X.X t ω) +
        (∑' u : ℝ≥0, if 0 < u ∧ u < t then Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0) := by
  filter_upwards
    [avram_p3_a_bvdrift_original_interval_raw_negative_jump_real_tsum X hBV]
    with ω hω
  intro t ht
  let f : ℝ≥0 → ℝ := fun u =>
    if 0 < u ∧ u ≤ t then Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0
  have hsum : Summable f :=
    (hω 0 t (show (0 : ℝ≥0) ≤ t from zero_le)).1
  have hsplit := hsum.tsum_eq_add_tsum_ite t
  have hterm : f t = Function.leftLim (fun z : ℝ≥0 => X.X z ω) t - X.X t ω := by
    simp [f, ht]
  have hstrict :
      (∑' u : ℝ≥0, if u = t then (0 : ℝ) else f u) =
      (∑' u : ℝ≥0, if 0 < u ∧ u < t then Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0) := by
    apply tsum_congr
    intro u
    by_cases hut : u = t
    · subst u
      simp
    · have hiff : (0 < u ∧ u ≤ t) ↔ (0 < u ∧ u < t) := by
        constructor
        · intro hu
          exact ⟨hu.1, lt_of_le_of_ne hu.2 hut⟩
        · intro hu
          exact ⟨hu.1, le_of_lt hu.2⟩
      simp [f, hut, hiff]
  change (∑' u : ℝ≥0, f u) =
    (Function.leftLim (fun z : ℝ≥0 => X.X z ω) t - X.X t ω) +
      (∑' u : ℝ≥0, if 0 < u ∧ u < t then Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0)
  rw [hterm, hstrict] at hsplit
  exact hsplit
