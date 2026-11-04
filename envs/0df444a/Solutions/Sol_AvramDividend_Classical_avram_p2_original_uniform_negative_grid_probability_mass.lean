-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_original_uniform_negative_grid_probability_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T06:52:43.423018+00:00
-- url     : https://prove2.me/submissions/9dc5d76b-a2f4-416c-a4de-f221e0b358a0

import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Positivity
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_original_negative_tail_unweighted_linear_smalltime_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Uniform bound on the actual source probability mass in n equal cells when
their combined duration is no more than T; no jump compensator is assumed. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (ε : ℝ) (hε : 0 < ε) (T : ℝ) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
        ∀ n : ℕ, (n : ℝ) * h ≤ T →
          (n : ℝ≥0∞) *
            P {ω : Ω | X.X (Real.toNNReal h) ω ≤ -ε} ≤
          ENNReal.ofReal (C * T) := by
  obtain ⟨C, hC, hRate⟩ :=
    avram_p2_original_negative_tail_unweighted_linear_smalltime_bound X ε hε
  refine ⟨C, hC, ?_⟩
  filter_upwards [hRate] with h hProb
  intro n hn
  calc
    (n : ℝ≥0∞) * P {ω : Ω | X.X (Real.toNNReal h) ω ≤ -ε} ≤
        (n : ℝ≥0∞) * ENNReal.ofReal (C * h) :=
      mul_le_mul_of_nonneg_left hProb (by positivity)
    _ = ENNReal.ofReal ((n : ℝ) * (C * h)) := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg n)]
      simp only [ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (C * T) := ENNReal.ofReal_le_ofReal (by
      calc
        (n : ℝ) * (C * h) = C * ((n : ℝ) * h) := by ring
        _ ≤ C * T := mul_le_mul_of_nonneg_left hn (le_of_lt hC))
