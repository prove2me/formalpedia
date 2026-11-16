-- Prove2me | solution 1 for AvramDividend.Classical.avram_a124_original_negative_Borel_physical_void_probability_exact_poisson_exponential_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T19:32:37.363553+00:00
-- url     : https://prove2.me/submissions/69838b14-27c8-4919-87bf-6edca80a47fe

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a122_original_arbitrary_Borel_mark_void_natural_time_power_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a123_original_arbitrary_negative_Borel_void_smalltime_rate_20261114
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_real_void_semigroup_exp_limit
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
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ)) :
    (P {ω : Ω |
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B) = 0}).toReal =
      Real.exp (-((T : ℝ) * (X.ν B).toReal)) := by
  let p : ℝ≥0 → ℝ := fun s =>
    (P {ω : Ω |
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 s ×ˢ B) = 0}).toReal
  have hPower : ∀ n : ℕ, 0 < n →
      p T = (p (T / (n : ℝ≥0))) ^ n := by
    intro n hn
    have hn0 : (n : ℝ≥0) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    have hTime : (n : ℝ≥0) * (T / (n : ℝ≥0)) = T := by
      field_simp [hn0]
    have hSource :=
      avram_a122_original_arbitrary_Borel_mark_void_natural_time_power_20261114
        X (T / (n : ℝ≥0)) B hB n
    dsimp at hSource
    rw [hTime] at hSource
    have hReal := congrArg ENNReal.toReal hSource
    simpa only [p, ENNReal.toReal_pow] using hReal
  have hSlope : Filter.Tendsto
      (fun n : ℕ =>
        (n : ℝ) * (1 - p (T / (n : ℝ≥0))))
      Filter.atTop (nhds ((T : ℝ) * (X.ν B).toReal)) := by
    simpa only [p] using
      (avram_a123_original_arbitrary_negative_Borel_void_smalltime_rate_20261114
        X hFinite T B hB hNeg)
  have hExp :=
    avram_wave7_06_real_void_semigroup_exp_limit
      p T (X.ν B).toReal hPower hSlope
  simpa only [p] using hExp
