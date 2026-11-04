-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_negative_band_occupied_cell_probability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:07:54.64895+00:00
-- url     : https://prove2.me/submissions/6003bd9c-f760-4741-b45e-9e61709a72b3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_intrinsic_future_borel_mark_void_event_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_intrinsic_marked_void_stationary_without_counter_premise

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The exact occupied source jump cell is the complement of its stationary void. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ℝ≥0) (n : ℕ) :
    P {ω : Ω |
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s (s + T) ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) ≠ 0} =
    1 - P {ω : Ω |
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0} := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  have hNX : ∀ ω, NX ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) := by
    intro ω
    rfl
  have hMeas : MeasurableSet
      {ω : Ω | NX ω
        (Ioc s (s + T) ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0} := by
    simpa only [NX] using
      (avram_wave7_06_original_intrinsic_future_borel_mark_void_event_measurable
        X s (s + T) (by simp) _ (by measurability))
  have hFin : P {ω : Ω | NX ω
      (Ioc s (s + T) ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0} ≠ ⊤ := by
    have hLe : P {ω : Ω | NX ω
        (Ioc s (s + T) ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0} ≤ 1 := by
      calc
        P {ω : Ω | NX ω
          (Ioc s (s + T) ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0} ≤
            P Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
    exact ne_top_of_le_ne_top (by simp) hLe
  have hStat :=
    avram_wave7_06_original_intrinsic_marked_void_stationary_without_counter_premise
      X NX hNX s T (Iic (-(1 / ((n : ℝ) + 1)))) (by measurability)
  change P {ω : Ω | NX ω
      (Ioc s (s + T) ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) ≠ 0} =
    1 - P {ω : Ω | NX ω
      (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0}
  calc
    P {ω : Ω | NX ω
        (Ioc s (s + T) ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) ≠ 0} =
      P {ω : Ω | NX ω
        (Ioc s (s + T) ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0}ᶜ := rfl
    _ = 1 - P {ω : Ω | NX ω
        (Ioc s (s + T) ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0} := by
      simpa using (measure_compl hMeas hFin)
    _ = 1 - P {ω : Ω | NX ω
        (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0} := by rw [hStat]
