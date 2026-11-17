-- Prove2me | solution 1 for AvramDividend.Classical.avram_a26_physical_void_probability_parameter_rate_20261116
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T07:53:56.509034+00:00
-- url     : https://prove2.me/submissions/2addd24c-ecfc-4c70-b873-162c1c51de31

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a123_original_arbitrary_negative_Borel_void_smalltime_rate_20261114
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ))
    (p : ℕ → unitInterval)
    (hp : ∀ n : ℕ, (p n : ℝ) =
      1 - (P {ω : Ω |
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 (T / (n : ℝ≥0)) ×ˢ B) = 0}).toReal) :
    Tendsto (fun n : ℕ => (n : ℝ) * (p n : ℝ))
      atTop (𝓝 ((T : ℝ) * (X.ν B).toReal)) := by
  have hfun : (fun n : ℕ => (n : ℝ) * (p n : ℝ)) =
      (fun n : ℕ => (n : ℝ) *
        (1 - (P {ω : Ω |
          ((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u, X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
            (Ioc 0 (T / (n : ℝ≥0)) ×ˢ B) = 0}).toReal)) := by
    funext n
    rw [hp n]
  rw [hfun]
  exact avram_a123_original_arbitrary_negative_Borel_void_smalltime_rate_20261114
    X hFinite T B hB hNeg
