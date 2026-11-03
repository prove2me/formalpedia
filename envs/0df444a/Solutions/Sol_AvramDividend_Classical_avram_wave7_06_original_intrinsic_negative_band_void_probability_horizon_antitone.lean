-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_intrinsic_negative_band_void_probability_horizon_antitone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T14:38:25.536007+00:00
-- url     : https://prove2.me/submissions/25b318a3-fb21-4033-a746-3ba835590cd3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_intrinsic_negative_band_void_split_adjacent_horizons

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Increasing the original source observation horizon decreases its negative-band void probability. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T S : ℝ≥0) (n : ℕ) :
    (let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
     let B : Set ℝ := Iic (-(1 / ((n : ℝ) + 1)))
     P {ω : Ω | NX ω (Ioc 0 (T + S) ×ˢ B) = 0} ≤
       P {ω : Ω | NX ω (Ioc 0 T ×ˢ B) = 0}) := by
  classical
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  let B : Set ℝ := Iic (-(1 / ((n : ℝ) + 1)))
  change P {ω : Ω | NX ω (Ioc 0 (T + S) ×ˢ B) = 0} ≤
    P {ω : Ω | NX ω (Ioc 0 T ×ˢ B) = 0}
  apply measure_mono
  intro ω hTotal
  exact ((avram_wave7_06_original_intrinsic_negative_band_void_split_adjacent_horizons
    X ω T S n).1 hTotal).1
