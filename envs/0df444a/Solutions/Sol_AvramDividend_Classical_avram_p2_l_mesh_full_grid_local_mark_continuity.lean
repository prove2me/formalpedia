-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_l_mesh_full_grid_local_mark_continuity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:29:13.818076+00:00
-- url     : https://prove2.me/submissions/c8bf8bf9-348f-45c9-a957-0b31842339bf

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_generic_finite_large_jumps_on_horizon
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_finite_jump_test_local_continuity
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_any_right_closed_uniform_locator_has_sided_limits
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_finite_right_closed_grid_locators_eventually_injective
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_uniform_test_zero_outside_all_large_jump_cells
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_finite_grid_sum_eq_selected_injective_cells

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology AvramDividend.Classical
open scoped NNReal BigOperators

/-- Full-grid marked-test convergence needs local continuity only at large
true jump marks; it allows discontinuous tests away from those marks. -/
theorem solution
    (Y : ℝ≥0 → ℝ) (T : ℝ≥0) (hT : 0 < T)
    (f : ℝ → ℝ) (ρ : ℝ) (hρ : 0 < ρ)
    (hfzero : ∀ z : ℝ, |z| < ρ → f z = 0)
    (hf : ∀ u : ℝ≥0, 0 < u → u ≤ T →
      ρ ≤ |Y u - Function.leftLim Y u| →
      ContinuousAt f (Y u - Function.leftLim Y u))
    (hL : ∀ t : ℝ≥0,
      Tendsto Y (𝓝[<] t) (𝓝 (Function.leftLim Y t)))
    (hR : ∀ t : ℝ≥0, ContinuousWithinAt Y (Ici t) t) :
    ∃ S : Finset ℝ≥0,
      (∀ u : ℝ≥0, u ∈ S ↔ 0 < u ∧ u ≤ T ∧
        ρ ≤ |Y u - Function.leftLim Y u|) ∧
      Tendsto (fun n : ℕ =>
        ∑ i ∈ Finset.range (n + 1),
          f (Y (((i + 1 : ℕ) : ℝ≥0) *
              (T / ((n : ℝ≥0) + 1))) -
            Y ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1)))))
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
  have hTimes : ∀ u ∈ S, 0 < u ∧ u ≤ T := by
    intro u hu
    exact ⟨((hS u).mp hu).1, ((hS u).mp hu).2.1⟩
  have hfS : ∀ u ∈ S, ContinuousAt f (Y u - Function.leftLim Y u) := by
    intro u hu
    obtain ⟨hu0, huT, huρ⟩ := (hS u).mp hu
    exact hf u hu0 huT huρ
  obtain ⟨j, hj, hsum⟩ :=
    avram_p2_l_mesh_finite_jump_test_local_continuity
      Y S T hT f hfS hTimes (fun u _ => hL u) (fun u _ => hR u)
  have hright : ∀ u ∈ S,
      Tendsto (fun n : ℕ =>
        (((j u n + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))))
        atTop (𝓝 u) := by
    intro u hu
    have hsided :=
      avram_p2_h_cadlag_any_right_closed_uniform_locator_has_sided_limits
        T u (j u) (fun n => ⟨(hj u hu n).2.1, (hj u hu n).2.2⟩)
    exact tendsto_nhds_of_tendsto_nhdsWithin hsided.2
  have hinj : ∀ᶠ n : ℕ in atTop,
      Set.InjOn (fun u => j u n) (S : Set ℝ≥0) :=
    avram_p2_h_cadlag_finite_right_closed_grid_locators_eventually_injective
      S (fun n u => j u n) T hright
  have hzero : ∀ᶠ n : ℕ in atTop,
      ∀ i ∈ Finset.range (n + 1),
      i ∉ S.image (fun u => j u n) →
      f (Y (((i + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) -
        Y ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1)))) = 0 :=
    avram_p2_h_cadlag_uniform_test_zero_outside_all_large_jump_cells
      Y T hT ρ hρ f hfzero S
      (fun t ht0 htT htlarge => (hS t).mpr ⟨ht0, htT, htlarge⟩)
      j hj (fun t _ => hL t) (fun t _ => hR t)
  have heq : (fun n : ℕ =>
      ∑ i ∈ Finset.range (n + 1),
        f (Y (((i + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) -
          Y ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))))) =ᶠ[atTop]
      (fun n : ℕ => ∑ u ∈ S,
        f (Y (((j u n + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) -
          Y ((j u n : ℝ≥0) * (T / ((n : ℝ≥0) + 1))))) := by
    filter_upwards [hinj, hzero] with n hni hnz
    exact avram_p2_h_cadlag_finite_grid_sum_eq_selected_injective_cells
      S n (fun u => j u n)
      (fun u hu => Nat.lt_succ_of_le (hj u hu n).1)
      hni (fun i => f (Y (((i + 1 : ℕ) : ℝ≥0) *
        (T / ((n : ℝ≥0) + 1))) -
        Y ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))))) hnz
  exact ⟨S, hS, hsum.congr' heq.symm⟩
