-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_obstruction_original_positive_probability_nojump_linear_source
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T07:26:03.788216+00:00
-- url     : https://prove2.me/submissions/e2d3b4aa-1f12-4ebb-b0e8-40c4048c342f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a82_original_finiteactivity_fullnegative_nojump_probability_20261114
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys75_original_zero_negative_mark_count_entire_source_drift
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_positive_markfree_event_survives_ae_linear_path
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) (T : ℝ≥0) :
    let E : Set Ω := {ω |
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ (X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iio (0 : ℝ)) = 0}
    0 < P {ω | ω ∈ E ∧
      (∀ t : ℝ≥0, t ≤ T → X.X t ω = (t : ℝ) * X.drift)} := by
  dsimp
  let E : Set Ω := {ω |
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ (X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ Iio (0 : ℝ)) = 0}
  have hProb : P E =
      ENNReal.ofReal (Real.exp
        (-((T : ℝ) * (X.ν (Iio (0 : ℝ))).toReal))) := by
    exact avram_a82_original_finiteactivity_fullnegative_nojump_probability_20261114
      X hFinite T
  have hPositive : 0 < P E := by
    rw [hProb]
    exact ENNReal.ofReal_pos.mpr (Real.exp_pos _)
  have hDrift := avram_bvb_phys75_original_zero_negative_mark_count_entire_source_drift
    X hX hBV T
  exact avram_bvb_obstruction_positive_markfree_event_survives_ae_linear_path
    P E (fun ω => ∀ t : ℝ≥0, t ≤ T →
      X.X t ω = (t : ℝ) * X.drift) hPositive hDrift
