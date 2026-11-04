-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_original_finite_significant_jump_finset
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:06:42.498602+00:00
-- url     : https://prove2.me/submissions/07559a78-5dac-4fc4-adca-35072378c230

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_finite_horizon_separated_jump_marks_finite_every_path

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal

/-- Every actual sample path and positive mark cutoff admit the exact finite
index set of genuine significant jumps in the source time interval. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (T : ℝ≥0) (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ F : Finset ℝ≥0, ∀ t : ℝ≥0,
      t ∈ F ↔ 0 < t ∧ t ≤ T ∧
        ρ ≤ |X.X t ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) t| := by
  let S : Set ℝ≥0 := {t | 0 < t ∧ t ≤ T ∧
    ρ ≤ |X.X t ω -
      Function.leftLim (fun v : ℝ≥0 => X.X v ω) t|}
  have hS : S.Finite := by
    simpa only [S, Real.dist_eq, sub_zero] using
      (avram_wave5_01_actual_source_finite_horizon_separated_jump_marks_finite_every_path
        X ω T ρ hρ)
  refine ⟨hS.toFinset, ?_⟩
  intro t
  simp only [Set.Finite.mem_toFinset]
  rfl
