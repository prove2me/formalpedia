-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_original_zero_cutoff_eq_full_jump_total
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:18:38.459974+00:00
-- url     : https://prove2.me/submissions/08e47b67-f2fa-4ebf-be98-1357d82337c6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- A zero size cutoff loses no mass from the actual negative left-jump
magnitude series, including zero increments. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (ω : Ω) :
    (∑' (v : ℝ≥0),
      if 0 < v ∧ v ≤ T ∧ (0 : ℝ≥0∞) < ENNReal.ofReal (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
      then ENNReal.ofReal (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω) else 0) =
    (∑' (v : ℝ≥0),
      if 0 < v ∧ v ≤ T then ENNReal.ofReal (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω) else 0) := by
  classical
  apply tsum_congr
  intro v
  by_cases hv : 0 < v
  · by_cases ht : v ≤ T
    · by_cases hj : (0 : ℝ≥0∞) <
        ENNReal.ofReal (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
      · simp [hv, ht, hj]
      · have hz :
          ENNReal.ofReal (Function.leftLim
            (fun z : ℝ≥0 => X.X z ω) v - X.X v ω) = 0 :=
          le_antisymm (le_of_not_gt hj) bot_le
        simp [hv, ht, hj, hz]
    · simp [hv, ht]
  · simp [hv]