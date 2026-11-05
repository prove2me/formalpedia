-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_l_mesh_strict_negative_compact_test_intrinsic_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T12:18:56.400701+00:00
-- url     : https://prove2.me/submissions/c0832338-d0b0-4456-a1c5-fbf476be2f2a

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_negative_support_has_strict_cutoff
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_compact_test_uniform_grid_intrinsic_jump_tendsto

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology AvramDividend.Classical
open scoped NNReal BigOperators Classical

/-- For compact continuous tests supported strictly below zero, the
original uniform-grid sum converges without a supplied cutoff parameter. -/
theorem solution
    (Y : ℝ≥0 → ℝ) (T : ℝ≥0) (hT : 0 < T)
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
    avram_p2_l_mesh_compact_test_uniform_grid_intrinsic_jump_tendsto
      Y T hT ρ hρ hL hR f hfcomp hfcont hf
  exact ⟨ρ, hρ, S, hS, hlim⟩
