-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_l_mesh_uniform_all_negative_mark_count_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:44:17.785508+00:00
-- url     : https://prove2.me/submissions/bff77e08-ae9a-4f51-8df3-d8d5d1de238f

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_generic_finite_large_jumps_on_horizon
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_eventually_nonzero_test_grid_count_le_large_jumps
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_finite_jump_test_local_continuity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology AvramDividend.Classical
open scoped NNReal BigOperators Classical

/-- A single sufficiently fine original grid controls the number of marked
cells for *every* separated negative set at once, without boundary conditions. -/
theorem solution
    (Y : ℝ≥0 → ℝ) (T : ℝ≥0) (hT : 0 < T)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hL : ∀ t : ℝ≥0,
      Tendsto Y (𝓝[<] t) (𝓝 (Function.leftLim Y t)))
    (hR : ∀ t : ℝ≥0, ContinuousWithinAt Y (Ici t) t) :
    ∃ S : Finset ℝ≥0,
      (∀ u : ℝ≥0, u ∈ S ↔ 0 < u ∧ u ≤ T ∧
        ρ ≤ |Y u - Function.leftLim Y u|) ∧
      ∀ᶠ n : ℕ in atTop, ∀ B : Set ℝ,
        B ⊆ Iic (-ρ) →
        ((Finset.range (n + 1)).filter (fun i : ℕ =>
          Y (((i + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) -
          Y ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ∈ B)).card ≤
        S.card := by
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
  obtain ⟨j, hj, _⟩ :=
    avram_p2_l_mesh_finite_jump_test_local_continuity
      Y S T hT (fun _ : ℝ => (0 : ℝ))
      (by intros; exact continuousAt_const)
      hTimes (fun u _ => hL u) (fun u _ => hR u)
  let f : ℝ → ℝ := fun z => if ρ ≤ |z| then 1 else 0
  have hfzero : ∀ z : ℝ, |z| < ρ → f z = 0 := by
    intro z hz
    simp [f, not_le.mpr hz]
  have hlarge : ∀ᶠ n : ℕ in atTop,
      ((Finset.range (n + 1)).filter (fun i =>
        f (Y (((i + 1 : ℕ) : ℝ≥0) *
          (T / ((n : ℝ≥0) + 1))) -
          Y ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1)))) ≠ 0)).card ≤
        S.card :=
    avram_p2_h_cadlag_eventually_nonzero_test_grid_count_le_large_jumps
      Y T hT ρ hρ f hfzero S
      (fun u hu0 huT huρ => (hS u).mpr ⟨hu0, huT, huρ⟩)
      j hj (fun t _ => hL t) (fun t _ => hR t)
  refine ⟨S, hS, ?_⟩
  filter_upwards [hlarge] with n hn B hBsep
  apply (Finset.card_le_card ?_).trans hn
  intro i hi
  obtain ⟨hir, hib⟩ := Finset.mem_filter.mp hi
  apply Finset.mem_filter.mpr
  refine ⟨hir, ?_⟩
  have hz :
      Y (((i + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) -
        Y ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ≤ -ρ := hBsep hib
  have hzero :
      Y (((i + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) -
        Y ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ≤ 0 := by linarith
  have hρabs : ρ ≤ |Y (((i + 1 : ℕ) : ℝ≥0) *
      (T / ((n : ℝ≥0) + 1))) -
      Y ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1)))| := by
    rw [abs_of_nonpos hzero]
    linarith
  have hρcast := hρabs
  simp only [Nat.cast_add, Nat.cast_one] at hρcast
  simp [f, Nat.cast_add, Nat.cast_one, hρcast]
