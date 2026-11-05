-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_l_mesh_compact_test_uniform_grid_intrinsic_jump_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T11:55:58.710951+00:00
-- url     : https://prove2.me/submissions/5b2dce7f-4783-41a0-a09a-b2f0013e057e

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_generic_finite_large_jumps_on_horizon
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_compact_test_mark_free_step_density
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_compact_test_convergence_of_step_approximations

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology AvramDividend.Classical
open scoped NNReal BigOperators Classical

/-- The genuine original uniform-grid marked-test sum converges to the
intrinsic finite cadlag jump sum for a compact continuous negative test. -/
theorem solution
    (Y : ℝ≥0 → ℝ) (T : ℝ≥0) (hT : 0 < T)
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
  let M : Finset ℝ := S.image (fun u => Y u - Function.leftLim Y u)
  have hApprox : ∀ η : ℝ, 0 < η →
      ∃ m : ℕ, ∃ a b c : Fin m → ℝ,
        (∀ i, b i ≤ -ρ) ∧
        (∀ (i : Fin m) (u : ℝ≥0), 0 < u → u ≤ T →
          ρ ≤ |Y u - Function.leftLim Y u| →
          Y u - Function.leftLim Y u ≠ a i ∧
            Y u - Function.leftLim Y u ≠ b i) ∧
        (∀ z : ℝ, |f z - (∑ i : Fin m,
          if z ∈ Ioc (a i) (b i) then c i else 0)| ≤ η) := by
    intro η hη
    obtain ⟨m, a, b, c, hb, havo, happ⟩ :=
      avram_p2_l_mesh_compact_test_mark_free_step_density
        M f ρ η hη hfcomp hfcont hf
    refine ⟨m, a, b, c, hb, ?_, happ⟩
    intro i u hu huT hjump
    have huS : u ∈ S := (hS u).2 ⟨hu, huT, hjump⟩
    have hm : Y u - Function.leftLim Y u ∈ M :=
      Finset.mem_image.mpr ⟨u, huS, rfl⟩
    exact ⟨fun heq => (havo i).1 (heq ▸ hm),
      fun heq => (havo i).2 (heq ▸ hm)⟩
  exact avram_p2_l_mesh_compact_test_convergence_of_step_approximations
    Y T hT ρ hρ hL hR f hf hApprox
