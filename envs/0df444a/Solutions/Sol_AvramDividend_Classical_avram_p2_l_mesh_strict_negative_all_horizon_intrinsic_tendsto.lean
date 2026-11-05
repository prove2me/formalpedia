-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_l_mesh_strict_negative_all_horizon_intrinsic_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T12:32:27.099879+00:00
-- url     : https://prove2.me/submissions/c143d37c-ea5f-4c28-85bb-79d1a4672f26

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_negative_support_has_strict_cutoff
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_compact_test_all_horizon_intrinsic_jump_tendsto

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology AvramDividend.Classical
open scoped NNReal BigOperators Classical

/-- The same source-exact original-grid theorem, resubmitted after a
transient platform PostgREST import-resolution failure in candidate 26546.
Its mathematical proof and all dependencies are unchanged. -/
theorem solution
    (Y : ℝ≥0 → ℝ) (T : ℝ≥0)
    (hL : ∀ t : ℝ≥0,
      Tendsto Y (𝓝[<] t) (𝓝 (Function.leftLim Y t)))
    (hR : ∀ t : ℝ≥0, ContinuousWithinAt Y (Ici t) t)
    (f : ℝ → ℝ) (hfcomp : HasCompactSupport f)
    (hfcont : Continuous f)
    (hneg : tsupport f ⊆ Iio (0 : ℝ)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ S : Finset ℝ≥0,
      (∀ u : ℝ≥0, u ∈ S ↔ 0 < u ∧ u ≤ T ∧
        ρ ≤ |Y u - Function.leftLim Y u|) ∧
      Tendsto (fun n : ℕ =>
        ∑ j ∈ Finset.range (n + 1),
          f (Y (((j + 1 : ℕ) : ℝ≥0) *
                (T / ((n : ℝ≥0) + 1))) -
            Y ((j : ℝ≥0) * (T / ((n : ℝ≥0) + 1)))))
        atTop (𝓝 (∑ u ∈ S, f (Y u - Function.leftLim Y u))) := by
  obtain ⟨ρ, hρ, hf⟩ :=
    avram_p2_l_mesh_negative_support_has_strict_cutoff f hneg
  obtain ⟨S, hS, hlim⟩ :=
    avram_p2_l_mesh_compact_test_all_horizon_intrinsic_jump_tendsto
      Y T ρ hρ hL hR f hfcomp hfcont hf
  exact ⟨ρ, hρ, S, hS, hlim⟩
