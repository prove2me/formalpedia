-- Prove2me | solution 1 for AvramDividend.Classical.avram_a119_original_arbitrary_negative_Borel_void_probability_semigroup_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T19:24:10.885873+00:00
-- url     : https://prove2.me/submissions/456321ac-a456-4b22-aaf5-1e27f8f40b31

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a118_original_arbitrary_Borel_mark_void_split_adjacent_horizons_20261114
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_intrinsic_future_borel_mark_void_event_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_intrinsic_future_mark_void_event_probability_factor
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_intrinsic_marked_void_stationary_without_counter_premise
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

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
    (s T : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B)
    (hPast : MeasurableSet[𝓕 s]
      {ω : Ω | NX ω (Ioc 0 s ×ˢ B) = 0}) :
    P {ω : Ω | NX ω (Ioc 0 (s + T) ×ˢ B) = 0} =
      P {ω : Ω | NX ω (Ioc 0 s ×ˢ B) = 0} *
      P {ω : Ω | NX ω (Ioc 0 T ×ˢ B) = 0} := by
  let V : Set Ω := {ω | NX ω (Ioc 0 s ×ˢ B) = 0}
  let W : Set Ω := {ω | NX ω (Ioc s (s + T) ×ˢ B) = 0}
  have hTime : s ≤ s + T := le_add_of_nonneg_right (bot_le : (0 : ℝ≥0) ≤ T)
  have hRaw : MeasurableSet V := by
    have hMeas :=
      avram_wave7_06_original_intrinsic_future_borel_mark_void_event_measurable
        X 0 s (bot_le : (0 : ℝ≥0) ≤ s) B hB
    simpa only [V, hNX] using hMeas
  have hFactor : P (V ∩ W) = P V * P W := by
    have hBase :=
      avram_wave7_06_original_intrinsic_future_mark_void_event_probability_factor
        X s (s + T) hTime B hB V hPast hRaw
    simpa only [V, W, hNX] using hBase
  have hSplit : {ω : Ω | NX ω (Ioc 0 (s + T) ×ˢ B) = 0} = V ∩ W := by
    ext ω
    have h :=
      avram_a118_original_arbitrary_Borel_mark_void_split_adjacent_horizons_20261114
        X ω s T B
    simpa only [V, W, hNX, Set.mem_setOf_eq, Set.mem_inter_iff] using h
  have hStationary :
      P W = P {ω : Ω | NX ω (Ioc 0 T ×ˢ B) = 0} := by
    simpa only [W] using
      (avram_wave7_06_original_intrinsic_marked_void_stationary_without_counter_premise
        X NX hNX s T B hB)
  change P {ω : Ω | NX ω (Ioc 0 (s + T) ×ˢ B) = 0} =
    P V * P {ω : Ω | NX ω (Ioc 0 T ×ˢ B) = 0}
  calc
    P {ω : Ω | NX ω (Ioc 0 (s + T) ×ˢ B) = 0} =
        P (V ∩ W) := by rw [hSplit]
    _ = P V * P W := hFactor
    _ = P V * P {ω : Ω | NX ω (Ioc 0 T ×ˢ B) = 0} := by
      rw [hStationary]
