-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p1_positive_energy_canonical_finite_rate_mark_exhaustion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T22:35:22.35135+00:00
-- url     : https://prove2.me/submissions/a5272450-ecd9-4f55-aee4-b63ddfdbc9e2

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
    (hpos : ∀ z, 0 < g z) :
    let B : ℕ → Set E := fun n => {z | (n : ℝ≥0∞)⁻¹ ≤ g z}
    (∀ n, MeasurableSet (B n)) ∧
    (∀ n, ν (B n) < ∞) ∧
    Monotone B ∧
    (⋃ n, B n) = Set.univ := by
  dsimp
  let B : ℕ → Set E := fun n => {z | (n : ℝ≥0∞)⁻¹ ≤ g z}
  have hm (n : ℕ) : MeasurableSet (B n) := by
    exact measurableSet_le measurable_const hg
  have hfin (n : ℕ) : ν (B n) < ∞ := by
    apply AvramDividend.Classical.avram_wave4_p1_positive_square_energy_threshold_finite_mark_intensity
      ν g hg henergy (B n) (hm n) ((n : ℝ≥0∞)⁻¹)
    · exact ENNReal.inv_pos.mpr (by simp)
    · intro z hz
      exact hz
  have hmono : Monotone B := by
    intro i j hij z hz
    exact le_trans (ENNReal.inv_le_inv' (by exact_mod_cast hij)) hz
  have hcover : (⋃ n, B n) = Set.univ := by
    ext z
    constructor
    · intro _; trivial
    · intro _
      have hevent : ∀ᶠ n : ℕ in Filter.atTop,
          ((n : ℝ≥0∞)⁻¹) < g z :=
        ENNReal.tendsto_inv_nat_nhds_zero.eventually
          (eventually_lt_nhds (hpos z))
      obtain ⟨n, hn⟩ := hevent.exists
      exact Set.mem_iUnion.mpr ⟨n, le_of_lt hn⟩
  exact ⟨hm, hfin, hmono, hcover⟩
