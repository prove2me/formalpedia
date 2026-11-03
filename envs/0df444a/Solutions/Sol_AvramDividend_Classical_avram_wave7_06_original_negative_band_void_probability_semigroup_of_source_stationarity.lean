-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_negative_band_void_probability_semigroup_of_source_stationarity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T20:53:35.296709+00:00
-- url     : https://prove2.me/submissions/8cbe170d-a952-4c44-b533-025a36dff2b3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_intrinsic_negative_band_void_split_adjacent_horizons
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_intrinsic_future_borel_mark_void_event_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_intrinsic_future_mark_void_event_probability_factor

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Original intrinsic negative-band no-jump probabilities form a
multiplicative semigroup once the early void is adapted and later void
stationarity is identified on the same original source space. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (NX : Ω → Measure (ℝ≥0 × ℝ))
    (hNX : ∀ ω, NX ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))
    (T S : ℝ≥0) (n : ℕ)
    (hPast : MeasurableSet[𝓕 T]
      {ω : Ω | NX ω
        (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0})
    (hStationary :
      P {ω : Ω | NX ω
        (Ioc T (T + S) ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0} =
      P {ω : Ω | NX ω
        (Ioc 0 S ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0}) :
    P {ω : Ω | NX ω
      (Ioc 0 (T + S) ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0} =
    P {ω : Ω | NX ω
      (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0} *
    P {ω : Ω | NX ω
      (Ioc 0 S ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0} := by
  let B : Set ℝ := Iic (-(1 / ((n : ℝ) + 1)))
  let V : Set Ω := {ω | NX ω (Ioc 0 T ×ˢ B) = 0}
  let W : Set Ω := {ω | NX ω (Ioc T (T + S) ×ˢ B) = 0}
  have hB : MeasurableSet B := measurableSet_Iic
  have hTime : T ≤ T + S := le_add_of_nonneg_right (bot_le : (0 : ℝ≥0) ≤ S)
  have hRaw : MeasurableSet V := by
    have hMeas :=
      avram_wave7_06_original_intrinsic_future_borel_mark_void_event_measurable
        X 0 T (bot_le : (0 : ℝ≥0) ≤ T) B hB
    simpa only [V, hNX] using hMeas
  have hFactor : P (V ∩ W) = P V * P W := by
    have hBase :=
      avram_wave7_06_original_intrinsic_future_mark_void_event_probability_factor
        X T (T + S) hTime B hB V hPast hRaw
    simpa only [V, W, hNX] using hBase
  have hSplit : {ω : Ω | NX ω (Ioc 0 (T + S) ×ˢ B) = 0} =
      V ∩ W := by
    ext ω
    have h :=
      avram_wave7_06_original_intrinsic_negative_band_void_split_adjacent_horizons
        X ω T S n
    simpa only [V, W, hNX, Set.mem_setOf_eq, Set.mem_inter_iff] using h
  change P {ω : Ω | NX ω (Ioc 0 (T + S) ×ˢ B) = 0} =
    P V * P {ω : Ω | NX ω (Ioc 0 S ×ˢ B) = 0}
  calc
    P {ω : Ω | NX ω (Ioc 0 (T + S) ×ˢ B) = 0} = P (V ∩ W) := by
      rw [hSplit]
    _ = P V * P W := hFactor
    _ = P V * P {ω : Ω | NX ω (Ioc 0 S ×ˢ B) = 0} := by
      rw [hStationary]
