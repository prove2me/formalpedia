-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_05_cantor_shifted_record_eq_true_shifted_sup_on_grid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T15:23:48.565633+00:00
-- url     : https://prove2.me/submissions/600a1a1f-5107-4976-9d40-009e538834ff

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_chat04_nat_pairing_rational_grid_coverage
import Theorems.Thm_AvramDividend_Classical_chat05_cantor_rational_schedule_dense
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_actual_shifted_levy_dense_prefix_eq_shiftedSup

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

/-- Cantor-sampled future Lévy increments recover the genuine shifted
running supremum at each strictly positive-denominator rational cash-grid endpoint. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (u : ℝ≥0)
    (n k : ℕ) (hn : 0 < n) :
    (let samples : ℕ → ℝ≥0 := fun j =>
       ((Nat.unpair j).2 : ℝ≥0) *
         (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)
     ⨆ j : ℕ,
       if samples j ≤ (k : ℝ≥0) * (n : ℝ≥0)⁻¹ then
         ENNReal.ofReal (X.X (u + samples j) ω - X.X u ω)
       else 0).toReal =
    sSup ((fun v : ℝ≥0 => X.X (u + v) ω - X.X u ω) ''
      Set.Icc 0 ((k : ℝ≥0) * (n : ℝ≥0)⁻¹)) := by
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
  exact avram_ws01e_b_actual_shifted_levy_dense_prefix_eq_shiftedSup
    X ω u samples hdense hzero
      ((k : ℝ≥0) * (n : ℝ≥0)⁻¹) hgrid
