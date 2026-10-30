-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_05_cantor_sampled_normalized_record_eq_runningSup_on_grid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T11:06:57.199344+00:00
-- url     : https://prove2.me/submissions/d05b3885-856d-4966-8ad9-507d0a0cc5dc

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_chat04_nat_pairing_rational_grid_coverage
import Theorems.Thm_AvramDividend_Classical_chat05_cantor_rational_schedule_dense
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_actual_levy_dense_prefix_eq_runningSup

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

/-- At every genuine rational dividend-mesh endpoint, the measurable Cantor
record of the normalized original Lévy path is its actual running supremum. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (n k : ℕ) (hn : 0 < n) :
    (let samples : ℕ → ℝ≥0 := fun j =>
       ((Nat.unpair j).2 : ℝ≥0) *
         (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)
     ⨆ j : ℕ,
       if samples j ≤ (k : ℝ≥0) * (n : ℝ≥0)⁻¹ then
         ENNReal.ofReal (X.X (samples j) ω - X.X 0 ω)
       else 0).toReal =
    runningSup X ((k : ℝ≥0) * (n : ℝ≥0)⁻¹) ω := by
  let samples : ℕ → ℝ≥0 := fun j =>
    ((Nat.unpair j).2 : ℝ≥0) *
      (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)
  have hdense : Dense (Set.range samples) := by
    simpa [samples] using chat05_cantor_rational_schedule_dense
  have hzero : (0 : ℝ≥0) ∈ Set.range samples := by
    refine ⟨Nat.pair 0 0, ?_⟩
    simp [samples]
  obtain ⟨j, hj⟩ := chat04_nat_pairing_rational_grid_coverage n k hn
  have hgrid :
      (k : ℝ≥0) * (n : ℝ≥0)⁻¹ ∈ Set.range samples := ⟨j, hj⟩
  simpa only [X.X_zero ω, sub_zero] using
    (avram_ws01e_b_actual_levy_dense_prefix_eq_runningSup
      X ω samples hdense hzero
        ((k : ℝ≥0) * (n : ℝ≥0)⁻¹) hgrid)
