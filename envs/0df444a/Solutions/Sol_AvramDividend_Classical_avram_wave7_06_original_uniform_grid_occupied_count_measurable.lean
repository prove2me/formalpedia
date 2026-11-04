-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_uniform_grid_occupied_count_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:27:52.403328+00:00
-- url     : https://prove2.me/submissions/d604ee49-219e-4e00-b4f4-090a431b8754

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_occupied_cell_indicator_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Finite actual-X marked-cell occupancy sums are source measurable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (NX : Ω → Measure (ℝ≥0 × ℝ))
    (hNX : ∀ ω, NX ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))
    (δ : ℝ≥0) (n m : ℕ) :
    Measurable (fun ω : Ω =>
      ∑ i ∈ Finset.range m,
        ({ω : Ω | NX ω
          (Ioc ((i : ℝ≥0) * δ) ((i : ℝ≥0) * δ + δ) ×ˢ
            Iic (-(1 / ((n : ℝ) + 1)))) ≠ 0}).indicator
          (fun _ => (1 : ENNReal)) ω) := by
  classical
  apply Finset.measurable_sum
  intro i hi
  have h :=
    avram_wave7_06_original_negative_band_occupied_cell_indicator_measurable
      X ((i : ℝ≥0) * δ) δ n
  simpa only [hNX] using h
