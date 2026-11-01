-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p1_null_zero_energy_canonical_mark_band_exhaustion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T22:42:01.321587+00:00
-- url     : https://prove2.me/submissions/a0f6867c-bbf6-4d2d-a11c-0d96586bcb87

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_positive_square_energy_threshold_finite_mark_intensity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped ENNReal

theorem solution
    {E : Type*} [MeasurableSpace E] (ν : Measure E)
    (g : E → ℝ≥0∞) (hg : Measurable g)
    (henergy : ∫⁻ z, g z ∂ν < ∞)
    (hzero_null : ν {z | g z = 0} = 0) :
    let B : ℕ → Set E := fun n =>
      {z | (n : ℝ≥0∞)⁻¹ ≤ g z} ∪ {z | g z = 0}
    (∀ n, MeasurableSet (B n)) ∧
    (∀ n, ν (B n) < ∞) ∧
    Monotone B ∧
    (⋃ n, B n) = Set.univ := by
  dsimp
  let Z : Set E := {z | g z = 0}
  let L : ℕ → Set E := fun n => {z | (n : ℝ≥0∞)⁻¹ ≤ g z}
  let B : ℕ → Set E := fun n => L n ∪ Z
  have hmL (n : ℕ) : MeasurableSet (L n) := by
    exact measurableSet_le measurable_const hg
  have hmZ : MeasurableSet Z := by
    change MeasurableSet (g ⁻¹' ({0} : Set ℝ≥0∞))
    exact hg (measurableSet_singleton (0 : ℝ≥0∞))
  have hm (n : ℕ) : MeasurableSet (B n) := (hmL n).union hmZ
  have hfL (n : ℕ) : ν (L n) < ∞ := by
    apply AvramDividend.Classical.avram_wave4_p1_positive_square_energy_threshold_finite_mark_intensity
      ν g hg henergy (L n) (hmL n) ((n : ℝ≥0∞)⁻¹)
    · exact ENNReal.inv_pos.mpr (by simp)
    · intro z hz
      exact hz
  have hfB (n : ℕ) : ν (B n) < ∞ := by
    have hupper : ν (B n) ≤ ν (L n) + ν Z := measure_union_le _ _
    exact lt_of_le_of_lt hupper (by simpa [Z, hzero_null] using hfL n)
  have hmono : Monotone B := by
    intro i j hij z hz
    rcases hz with hlev | hz
    · exact Or.inl (le_trans (ENNReal.inv_le_inv' (by exact_mod_cast hij)) hlev)
    · exact Or.inr hz
  have hcover : (⋃ n, B n) = Set.univ := by
    ext z
    constructor
    · intro _; trivial
    · intro _
      by_cases hz : g z = 0
      · exact Set.mem_iUnion.mpr ⟨0, Or.inr hz⟩
      · have hpos : 0 < g z := pos_iff_ne_zero.mpr hz
        have hevent : ∀ᶠ n : ℕ in Filter.atTop,
            ((n : ℝ≥0∞)⁻¹) < g z :=
          ENNReal.tendsto_inv_nat_nhds_zero.eventually
            (eventually_lt_nhds hpos)
        obtain ⟨n, hn⟩ := hevent.exists
        exact Set.mem_iUnion.mpr ⟨n, Or.inl (le_of_lt hn)⟩
  exact ⟨hm, hfB, hmono, hcover⟩
