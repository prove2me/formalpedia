-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_l_mesh_compact_test_all_horizon_intrinsic_jump_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T12:13:05.512484+00:00
-- url     : https://prove2.me/submissions/f9de63cb-95d6-4740-b4d6-332cc93db142

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_compact_test_uniform_grid_intrinsic_jump_tendsto

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology AvramDividend.Classical
open scoped NNReal BigOperators Classical

/-- The original uniform-grid cadlag test convergence includes the
degenerate zero horizon, where every original grid increment vanishes. -/
theorem solution
    (Y : ℝ≥0 → ℝ) (T : ℝ≥0)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hL : ∀ t : ℝ≥0,
      Tendsto Y (𝓝[<] t) (𝓝 (Function.leftLim Y t)))
    (hR : ∀ t : ℝ≥0, ContinuousWithinAt Y (Ici t) t)
    (f : ℝ → ℝ) (hfcomp : HasCompactSupport f)
    (hfcont : Continuous f)
    (hf : ∀ z : ℝ, -ρ < z → f z = 0) :
    ∃ S : Finset ℝ≥0,
      (∀ u : ℝ≥0, u ∈ S ↔ 0 < u ∧ u ≤ T ∧
        ρ ≤ |Y u - Function.leftLim Y u|) ∧
      Tendsto (fun n : ℕ =>
        ∑ j ∈ Finset.range (n + 1),
          f (Y (((j + 1 : ℕ) : ℝ≥0) *
                (T / ((n : ℝ≥0) + 1))) -
            Y ((j : ℝ≥0) * (T / ((n : ℝ≥0) + 1)))))
        atTop (𝓝 (∑ u ∈ S, f (Y u - Function.leftLim Y u))) := by
  by_cases hT : 0 < T
  · exact avram_p2_l_mesh_compact_test_uniform_grid_intrinsic_jump_tendsto
      Y T hT ρ hρ hL hR f hfcomp hfcont hf
  · have hT0 : T = 0 := le_antisymm (le_of_not_gt hT) zero_le
    have hf0 : f 0 = 0 := hf 0 (by linarith)
    refine ⟨∅, ?_, ?_⟩
    · intro u
      constructor
      · intro hu
        have hfalse : False := by simpa using hu
        exact hfalse.elim
      · rintro ⟨hu, huT, _⟩
        have huT0 : u ≤ 0 := by simpa [hT0] using huT
        exact (not_lt_of_ge huT0 hu).elim
    · have hlim : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (0 : ℝ)) :=
        tendsto_const_nhds
      simpa [hT0, hf0] using hlim
