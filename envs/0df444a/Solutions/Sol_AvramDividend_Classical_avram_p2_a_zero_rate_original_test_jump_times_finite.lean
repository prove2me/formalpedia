-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_original_test_jump_times_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T17:20:04.79862+00:00
-- url     : https://prove2.me/submissions/828e9190-f5a6-4191-9dec-b270c0fd31f1

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_finite_horizon_separated_jump_marks_finite_every_path

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Only finitely many original jumps contribute to any test vanishing near zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (T : ℝ≥0) (ε : ℝ) (hε : 0 < ε)
    (f : ℝ → ℝ) (hf : ∀ y : ℝ, dist y 0 < ε → f y = 0) :
    {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
      f (X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) ≠ 0}.Finite := by
  apply (avram_wave5_01_actual_source_finite_horizon_separated_jump_marks_finite_every_path
    X ω T ε hε).subset
  rintro u ⟨hu0, huT, hfne⟩
  refine ⟨hu0, huT, ?_⟩
  by_contra hnot
  have hlt : dist (X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) 0 < ε := lt_of_not_ge hnot
  exact hfne (hf _ hlt)
