-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_negative_band_void_semigroup_without_stationary_hypothesis
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T23:43:58.818856+00:00
-- url     : https://prove2.me/submissions/4bb247e5-d1dd-4257-849f-54d20d153113

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_void_probability_semigroup_of_source_stationarity
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_intrinsic_marked_void_stationary_without_counter_premise

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Genuine source void time semigroup: stationarity follows from the
original process and a universal càdlàg marked-count functional. -/
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
        (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0}) :
    P {ω : Ω | NX ω
      (Ioc 0 (T + S) ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0} =
    P {ω : Ω | NX ω
      (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0} *
    P {ω : Ω | NX ω
      (Ioc 0 S ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0} := by
  let B : Set ℝ := Iic (-(1 / ((n : ℝ) + 1)))
  have hB : MeasurableSet B := measurableSet_Iic
  have hStationary :
      P {ω : Ω | NX ω (Ioc T (T + S) ×ˢ B) = 0} =
      P {ω : Ω | NX ω (Ioc 0 S ×ˢ B) = 0} :=
    avram_wave7_06_original_intrinsic_marked_void_stationary_without_counter_premise
      X NX hNX T S B hB
  exact
    avram_wave7_06_original_negative_band_void_probability_semigroup_of_source_stationarity
      X NX hNX T S n hPast (by simpa only [B] using hStationary)

-- New verifier implementation identity; exact original-source semigroup proof preserved.
