-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_separated_borel_nu_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:27:16.764519+00:00
-- url     : https://prove2.me/submissions/2bd2489e-0974-4ff3-b690-a22587ac7a0d

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.NormNum
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_negative_levy_mark_tail_finite_mass_at_every_small_threshold

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Every separated negative Borel band has finite genuine source Lévy mass,
including thresholds larger than one. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (B : Set ℝ) (hB : MeasurableSet B)
    (ε : ℝ) (hε : 0 < ε) (hBsep : B ⊆ Iic (-ε)) :
    X.ν B < ⊤ := by
  let δ : ℝ := min ε 1
  have hδ : 0 < δ := lt_min hε (by norm_num)
  have hδone : δ ≤ 1 := min_le_right ε 1
  have hδeps : δ ≤ ε := min_le_left ε 1
  have hTail : X.ν (Iic (-δ)) < ⊤ :=
    avram_wave7_02_original_negative_levy_mark_tail_finite_mass_at_every_small_threshold
      X.ν X.ν_integrable δ hδ hδone
  have hSub : B ⊆ Iic (-δ) := by
    intro z hz
    exact le_trans (hBsep hz) (neg_le_neg hδeps)
  exact lt_of_le_of_lt (measure_mono hSub) hTail
