-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_intrinsic_negative_band_void_natural_time_power
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:48:12.166979+00:00
-- url     : https://prove2.me/submissions/b007e265-c4ba-42a2-bfbf-c09b39000f02

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_intrinsic_negative_band_void_unconditional_semigroup
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_intrinsic_negative_band_zero_horizon_measure_univ

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Repeated original-filtration void-semigroup factorisation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (n k : ℕ) :
    (let p : ℝ≥0 → ENNReal := fun s =>
      P {ω : Ω |
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 s ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0}
     p ((k : ℝ≥0) * T) = (p T) ^ k) := by
  classical
  let p : ℝ≥0 → ENNReal := fun s =>
    P {ω : Ω |
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 s ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0}
  have hsem : ∀ s t : ℝ≥0, p (s + t) = p s * p t := by
    intro s t
    simpa only [p] using
      (avram_wave7_06_original_intrinsic_negative_band_void_unconditional_semigroup X s t n)
  have hzero : p 0 = 1 := by
    letI : IsProbabilityMeasure P := X.isProbability
    simpa [p] using
      (avram_wave7_06_original_intrinsic_negative_band_zero_horizon_measure_univ X n)
  change p ((k : ℝ≥0) * T) = (p T) ^ k
  induction k with
  | zero =>
      simpa using hzero
  | succ j ih =>
      have htime : (((j + 1 : ℕ) : ℝ≥0) * T) =
          ((j : ℝ≥0) * T) + T := by
        rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
      calc
        p (((j + 1 : ℕ) : ℝ≥0) * T) =
            p (((j : ℝ≥0) * T) + T) := by rw [htime]
        _ = p ((j : ℝ≥0) * T) * p T := hsem _ _
        _ = (p T) ^ (j + 1) := by rw [ih, pow_succ]
