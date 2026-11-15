-- Prove2me | solution 1 for AvramDividend.Classical.avram_a87_original_fullnegative_void_probability_time_semigroup_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T17:24:10.576134+00:00
-- url     : https://prove2.me/submissions/0fe69ac3-f4bb-498d-b74a-1fb4c419c164

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a82_original_finiteactivity_fullnegative_nojump_probability_20261114
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) (T S : ℝ≥0) :
    P {ω : Ω |
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (T + S) ×ˢ Iio (0 : ℝ)) = 0} =
      P {ω : Ω |
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iio (0 : ℝ)) = 0} *
      P {ω : Ω |
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 S ×ˢ Iio (0 : ℝ)) = 0} := by
  have hTS :=
    avram_a82_original_finiteactivity_fullnegative_nojump_probability_20261114
      X hFinite (T + S)
  have hT :=
    avram_a82_original_finiteactivity_fullnegative_nojump_probability_20261114
      X hFinite T
  have hS :=
    avram_a82_original_finiteactivity_fullnegative_nojump_probability_20261114
      X hFinite S
  rw [hTS, hT, hS]
  rw [← ENNReal.ofReal_mul (le_of_lt (Real.exp_pos _))]
  congr 1
  rw [← Real.exp_add]
  congr 1
  push_cast
  ring
