-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_uniform_grid_occupied_cell_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:27:48.680116+00:00
-- url     : https://prove2.me/submissions/3112ab03-633e-4bbb-8bb3-2174ca9b48c2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_occupied_cell_indicator_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Every source uniform-grid occupancy indicator is measurable on the same Ω. -/
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
    ∀ i ∈ Finset.range m, Measurable
      (fun ω : Ω =>
        ({ω : Ω | NX ω
          (Ioc ((i : ℝ≥0) * δ) ((i : ℝ≥0) * δ + δ) ×ˢ
            Iic (-(1 / ((n : ℝ) + 1)))) ≠ 0}).indicator
          (fun _ => (1 : ENNReal)) ω) := by
  intro i hi
  have h :=
    avram_wave7_06_original_negative_band_occupied_cell_indicator_measurable
      X ((i : ℝ≥0) * δ) δ n
  simpa only [hNX] using h
