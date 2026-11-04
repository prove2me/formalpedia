-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_h_cadlag_exact_mesh_sum_from_positive_time_left_limits
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:51:37.98859+00:00
-- url     : https://prove2.me/submissions/1e1ae8fb-e729-47fb-bede-57dbf2324a36

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_strict_left_limit_at_zero_is_vacuous
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_exact_mesh_sum_tends_finite_nonzero_test_jumps

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology AvramDividend.Classical
open scoped NNReal BigOperators

/-- The exact finite actual jump equality under the standard
càdlàg interface, which needs left limits only at positive times. -/
theorem solution
    (Y : ℝ≥0 → ℝ) (T : ℝ≥0) (hT : 0 < T)
    (f : ℝ → ℝ) (hf : Continuous f)
    (hneg : tsupport f ⊆ Set.Iio (0 : ℝ))
    (hL : ∀ t : ℝ≥0, 0 < t →
      Tendsto Y (𝓝[<] t) (𝓝 (Function.leftLim Y t)))
    (hR : ∀ t : ℝ≥0, ContinuousWithinAt Y (Ici t) t) :
    ∃ F : Finset ℝ≥0,
      (∀ u : ℝ≥0, u ∈ F ↔ 0 < u ∧ u ≤ T ∧
        f (Y u - Function.leftLim Y u) ≠ 0) ∧
      Tendsto (fun n : ℕ =>
        ∑ i ∈ Finset.range (n + 1),
          f (Y (((i + 1 : ℕ) : ℝ≥0) *
              (T / ((n : ℝ≥0) + 1))) -
            Y ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1)))))
        atTop (𝓝 (∑ u ∈ F, f (Y u - Function.leftLim Y u))) := by
  have hAll : ∀ t : ℝ≥0,
      Tendsto Y (𝓝[<] t) (𝓝 (Function.leftLim Y t)) := by
    intro t
    by_cases hz : t = 0
    · subst t
      exact avram_p2_h_cadlag_strict_left_limit_at_zero_is_vacuous Y
    · exact hL t (lt_of_le_of_ne (show (0 : ℝ≥0) ≤ t from zero_le) (Ne.symm hz))
  exact avram_p2_h_cadlag_exact_mesh_sum_tends_finite_nonzero_test_jumps
    Y T hT f hf hneg hAll hR
