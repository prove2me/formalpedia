-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_l_mesh_cadlag_selected_mark_avoiding_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T09:03:11.643+00:00
-- url     : https://prove2.me/submissions/2641512f-60da-4b6f-8e10-0a3f56a3bdd2

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_generic_finite_large_jumps_on_horizon
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_finite_negative_marks_avoid_interval_point

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology AvramDividend.Classical
open scoped NNReal BigOperators Classical

/-- Between any two distinct real marks one can place a cutoff avoiding
every significant original jump mark of a cadlag path on the horizon. -/
theorem solution
    (Y : ℝ≥0 → ℝ) (T : ℝ≥0)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hL : ∀ t : ℝ≥0,
      Tendsto Y (𝓝[<] t) (𝓝 (Function.leftLim Y t)))
    (hR : ∀ t : ℝ≥0, ContinuousWithinAt Y (Ici t) t)
    (a b : ℝ) (hab : a < b) :
    ∃ c : ℝ, a < c ∧ c < b ∧
      ∀ u : ℝ≥0, 0 < u → u ≤ T →
        ρ ≤ |Y u - Function.leftLim Y u| →
          Y u - Function.leftLim Y u ≠ c := by
  classical
  let Q : Set ℝ≥0 := {u | 0 < u ∧ u ≤ T ∧
    ρ ≤ dist (Y u - Function.leftLim Y u) 0}
  have hQ : Q.Finite :=
    avram_p2_h_cadlag_generic_finite_large_jumps_on_horizon
      Y hR (fun t _ => hL t) T ρ hρ
  let S : Finset ℝ≥0 := hQ.toFinset
  have hS (u : ℝ≥0) : u ∈ S ↔ 0 < u ∧ u ≤ T ∧
      ρ ≤ |Y u - Function.leftLim Y u| := by
    simpa only [S, Q, Set.mem_setOf_eq, Real.dist_eq, sub_zero]
      using (hQ.mem_toFinset (a := u))
  let marks : Finset ℝ := S.image (fun u => Y u - Function.leftLim Y u)
  obtain ⟨c, hac, hcb, hc⟩ :=
    avram_p2_l_mesh_finite_negative_marks_avoid_interval_point
      marks a b hab
  refine ⟨c, hac, hcb, ?_⟩
  intro u hu hT hlarge hEq
  apply hc
  apply Finset.mem_image.mpr
  exact ⟨u, (hS u).2 ⟨hu, hT, hlarge⟩, hEq⟩
