-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_uniform_negative_band_grid_occupied_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:10:02.898781+00:00
-- url     : https://prove2.me/submissions/3b502e3e-25be-43be-9830-4bb8bc4b9542

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_finite_grid_equal_cell_means_lintegral
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_occupied_cell_lintegral

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Source occupied-cell expectations sum over equal-width genuine jump rectangles. -/
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
    (δ : ℝ≥0) (n m : ℕ)
    (hCellMeas : ∀ i ∈ Finset.range m, Measurable
      (fun ω : Ω =>
        ({ω : Ω | NX ω
          (Ioc ((i : ℝ≥0) * δ) ((i : ℝ≥0) * δ + δ) ×ˢ
            Iic (-(1 / ((n : ℝ) + 1)))) ≠ 0}).indicator
          (fun _ => (1 : ENNReal)) ω)) :
    (∫⁻ ω, ∑ i ∈ Finset.range m,
      ({ω : Ω | NX ω
        (Ioc ((i : ℝ≥0) * δ) ((i : ℝ≥0) * δ + δ) ×ˢ
          Iic (-(1 / ((n : ℝ) + 1)))) ≠ 0}).indicator
        (fun _ => (1 : ENNReal)) ω ∂P) =
      (m : ENNReal) *
        (1 - P {ω : Ω | NX ω
          (Ioc 0 δ ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0}) := by
  classical
  let F : ℕ → Ω → ENNReal := fun i ω =>
    ({ω : Ω | NX ω
      (Ioc ((i : ℝ≥0) * δ) ((i : ℝ≥0) * δ + δ) ×ˢ
        Iic (-(1 / ((n : ℝ) + 1)))) ≠ 0}).indicator
      (fun _ => (1 : ENNReal)) ω
  let q : ENNReal := 1 - P {ω : Ω | NX ω
    (Ioc 0 δ ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0}
  have hEach : ∀ i ∈ Finset.range m,
      (∫⁻ ω, F i ω ∂P) = q := by
    intro i hi
    have h :=
      avram_wave7_06_original_negative_band_occupied_cell_lintegral
        X ((i : ℝ≥0) * δ) δ n
    simpa only [F, q, hNX] using h
  have hMeas : ∀ i ∈ Finset.range m, Measurable (F i) := by
    intro i hi
    exact hCellMeas i hi
  have hSum :=
    avram_wave7_06_finite_grid_equal_cell_means_lintegral
      P m F q hMeas hEach
  simpa only [F, q] using hSum
