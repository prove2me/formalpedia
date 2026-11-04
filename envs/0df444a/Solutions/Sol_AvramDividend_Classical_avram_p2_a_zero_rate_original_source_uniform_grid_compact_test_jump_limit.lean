-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_original_source_uniform_grid_compact_test_jump_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:41:47.149316+00:00
-- url     : https://prove2.me/submissions/7916abc8-e814-4225-9b5a-da691806d36e

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_uniform_full_grid_compact_test_limit
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_finite_significant_jump_finset
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_positive_horizon_to_closed_significant_jumps
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_cadlag_regular_all_times
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal

/-- On the exact original Levy sample path, the unmodified uniform-grid
compact-jump-test sum converges to the finite true positive-time jump sum. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (T : ℝ≥0) (hT : 0 < T)
    (ρ : ℝ) (hρ : 0 < ρ)
    (f : ℝ → ℝ) (hf : Continuous f)
    (hvanish : ∀ z : ℝ, |z| < ρ → f z = 0) :
    ∃ F : Finset ℝ≥0,
      (∀ t ∈ F, 0 < t ∧ t ≤ T) ∧
      Tendsto (fun n : ℕ =>
        ∑ i ∈ Finset.range (n + 1),
          f (X.X (((i + 1 : ℕ) : ℝ≥0) *
              (T / ((n : ℝ≥0) + 1))) ω -
            X.X ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω))
        atTop (𝓝 (∑ t ∈ F,
          f (X.X t ω -
            Function.leftLim (fun u : ℝ≥0 => X.X u ω) t))) := by
  obtain ⟨F, hF⟩ :=
    avram_p2_a_zero_rate_original_finite_significant_jump_finset
      X ω T ρ hρ
  have hbounds : ∀ t ∈ F, 0 < t ∧ t ≤ T := by
    intro t ht
    exact ⟨((hF t).mp ht).1, ((hF t).mp ht).2.1⟩
  have hpos : ∀ t ∈ F, 0 < t := fun t ht => (hbounds t ht).1
  have hbound : ∀ t ∈ F, t ≤ T := fun t ht => (hbounds t ht).2
  let Y : ℝ≥0 → ℝ := fun t => X.X t ω
  have hzero : Y 0 = Function.leftLim Y 0 := by
    have h : ContinuousWithinAt Y (Iic (0 : ℝ≥0)) 0 := by
      have hset : Iic (0 : ℝ≥0) = {0} := by
        ext t
        simp only [mem_Iic, mem_singleton_iff]
        exact ⟨fun ht => le_antisymm ht (show (0 : ℝ≥0) ≤ t from bot_le), fun ht => ht.le⟩
      change ContinuousWithinAt Y (Iic (0 : ℝ≥0)) 0
      rw [hset]
      exact continuousWithinAt_singleton
    exact h.leftLim_eq.symm
  have hcover : ∀ t ∈ Icc (0 : ℝ≥0) T,
      ρ ≤ |Y t - Function.leftLim Y t| → t ∈ F := by
    apply avram_p2_a_zero_rate_positive_horizon_to_closed_significant_jumps
      Y T ρ hρ hzero F
    intro t ht hlarge
    exact (hF t).mpr ⟨ht.1, ht.2, hlarge⟩
  obtain ⟨hL, hR⟩ :=
    avram_p2_a_zero_rate_original_cadlag_regular_all_times X ω
  refine ⟨F, hbounds, ?_⟩
  exact avram_p2_a_zero_rate_original_uniform_full_grid_compact_test_limit
    Y T hT hL hR ρ hρ F hcover hpos hbound f hf hvanish
