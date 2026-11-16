-- Prove2me | solution 1 for AvramDividend.Classical.avram_a123_original_arbitrary_negative_Borel_void_smalltime_rate_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T10:00:36.03491+00:00
-- url     : https://prove2.me/submissions/b1af6dc5-f9ed-478e-bb13-807c5fcd6a5c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a25_original_negative_Borel_void_quadratic_sandwich_20261115
import Theorems.Thm_AvramDividend_Classical_avram_a25_quadratic_void_deficit_squeeze_limit_20261115
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Physical marked-count void rate from a quadratic source occupancy estimate. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ)) :
    Filter.Tendsto
      (fun n : ℕ =>
        ((n : ℕ) : ℝ) * (1 -
          (P {ω : Ω |
            ((Measure.count.restrict {u : ℝ≥0 |
              0 < u ∧ X.X u ω -
                Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
              (fun u : ℝ≥0 => (u,
                X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
              (Ioc 0 (T / (n : ℝ≥0)) ×ˢ B) = 0}).toReal))
      Filter.atTop (nhds ((T : ℝ) * (X.ν B).toReal)) := by
  let rate : ℝ := (T : ℝ) * (X.ν B).toReal
  let q : ℕ → ℝ := fun n =>
    1 - (P {ω : Ω |
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (T / (n : ℝ≥0)) ×ˢ B) = 0}).toReal
  have hb :
      ∀ᶠ n in (Filter.atTop : Filter ℕ),
        rate - (rate ^ 2 / 2) * (1 / ((n : ℕ) : ℝ)) ≤
            ((n : ℕ) : ℝ) * q n ∧
          ((n : ℕ) : ℝ) * q n ≤ rate :=
    avram_a25_original_negative_Borel_void_quadratic_sandwich_20261115
      X hFinite T B hB hNeg
  simpa only [rate, q] using
    (avram_a25_quadratic_void_deficit_squeeze_limit_20261115 rate q hb)
