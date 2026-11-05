-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_l_mesh_finite_negative_intervals_counts_eventually_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:55:58.032996+00:00
-- url     : https://prove2.me/submissions/7cad98ea-0de1-4dc4-b105-c05f31dee37f

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_generic_finite_large_jumps_on_horizon
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_negative_interval_endpoint_avoiding_exact_count

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology AvramDividend.Classical
open scoped NNReal BigOperators Classical

/-- A finite interval histogram has the exact intrinsic jump counts once
the mesh is fine enough, if each interval endpoint avoids actual jumps. -/
theorem solution {ι : Type*} [Fintype ι]
    (Y : ℝ≥0 → ℝ) (T : ℝ≥0) (hT : 0 < T)
    (a b : ι → ℝ) (ρ : ℝ) (hρ : 0 < ρ)
    (hbneg : ∀ i, b i ≤ -ρ)
    (hEndpoint : ∀ (i : ι) (u : ℝ≥0), 0 < u → u ≤ T →
      ρ ≤ |Y u - Function.leftLim Y u| →
      Y u - Function.leftLim Y u ≠ a i ∧
        Y u - Function.leftLim Y u ≠ b i)
    (hL : ∀ t : ℝ≥0,
      Tendsto Y (𝓝[<] t) (𝓝 (Function.leftLim Y t)))
    (hR : ∀ t : ℝ≥0, ContinuousWithinAt Y (Ici t) t) :
    ∃ S : Finset ℝ≥0,
      (∀ u : ℝ≥0, u ∈ S ↔ 0 < u ∧ u ≤ T ∧
        ρ ≤ |Y u - Function.leftLim Y u|) ∧
      ∀ᶠ n : ℕ in atTop, ∀ i : ι,
        ((Finset.range (n + 1)).filter (fun j : ℕ =>
          Y (((j + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) -
          Y ((j : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ∈
            Ioc (a i) (b i))).card =
        (S.filter (fun u => Y u - Function.leftLim Y u ∈
          Ioc (a i) (b i))).card := by
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
  refine ⟨S, hS, ?_⟩
  have hEach (i : ι) : ∀ᶠ n : ℕ in atTop,
      ((Finset.range (n + 1)).filter (fun j : ℕ =>
        Y (((j + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) -
        Y ((j : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ∈
          Ioc (a i) (b i))).card =
      (S.filter (fun u => Y u - Function.leftLim Y u ∈
        Ioc (a i) (b i))).card := by
    obtain ⟨Si, hSi, hi⟩ :=
      avram_p2_l_mesh_negative_interval_endpoint_avoiding_exact_count
        Y T hT (a i) (b i) ρ hρ (hbneg i) (hEndpoint i) hL hR
    have heq : Si = S := by
      ext u
      exact (hSi u).trans (hS u).symm
    simpa only [heq] using hi
  have hAll (s : Finset ι) : ∀ᶠ n : ℕ in atTop,
      ∀ i ∈ s,
        ((Finset.range (n + 1)).filter (fun j : ℕ =>
          Y (((j + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) -
          Y ((j : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ∈
            Ioc (a i) (b i))).card =
        (S.filter (fun u => Y u - Function.leftLim Y u ∈
          Ioc (a i) (b i))).card := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s his ih =>
      filter_upwards [hEach i, ih] with n h_i h_s j hj
      rcases Finset.mem_insert.mp hj with hji | hjs
      · subst j
        exact h_i
      · exact h_s j hjs
  filter_upwards [hAll Finset.univ] with n hn
  exact fun i => hn i (Finset.mem_univ i)
