-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_e_compensator_original_grid_pair_rate_sum_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T13:41:32.431682+00:00
-- url     : https://prove2.me/submissions/4faa3e49-d2bd-4edd-a15a-0b20c8fcad98

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_grid_pair_lintegral_finite_sum
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_past_future_marked_pair_one_cell

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Every finite original grid pair sum has an explicit Lévy-rate expectation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (m : ℕ) (s t : Fin m → ℝ≥0) (hst : ∀ i, s i ≤ t i) (n : ℕ) :
    let B : Set ℝ := Iic (-(1 / ((n : ℝ) + 1)))
    let N : ℝ≥0 → ℝ≥0 → Ω → ℝ≥0∞ := fun a b ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc a b ×ˢ B)
    (∫⁻ ω, ∑ i : Fin m, N 0 (s i) ω * N (s i) (t i) ω ∂P) =
      ∑ i : Fin m, ((s i : ℝ≥0∞) * X.ν B) *
        (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν B) := by
  intro B N
  calc
    (∫⁻ ω, ∑ i : Fin m, N 0 (s i) ω * N (s i) (t i) ω ∂P) =
        ∑ i : Fin m, ∫⁻ ω, N 0 (s i) ω * N (s i) (t i) ω ∂P := by
      simpa only [] using
        (avram_p4_f_assembly_original_grid_pair_lintegral_finite_sum X m s t n)
    _ = ∑ i : Fin m, ((s i : ℝ≥0∞) * X.ν B) *
          (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν B) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      simpa only [] using
        (avram_p4_f_assembly_original_past_future_marked_pair_one_cell
          X (s i) (t i) (hst i) n)
