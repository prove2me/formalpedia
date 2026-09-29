-- Prove2me | solution 1 for Freiman.upper_path_shrinks
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T21:20:18.395468+00:00
-- url     : https://prove2.me/submissions/52b1514a-ddcf-4d63-9c88-a069af80a7ca

import Definitions.Def_Freiman_upperModel

open Freiman Filter

private theorem normal_tree_length_positive
    (T : List Bool → upperInterval) (hT : upperNormalTree T) (w : List Bool) :
    0 < upperLength (T w) := by
  rcases hT w with ⟨hl, hr, hg, hpl, hpr, _, _⟩
  unfold upperLength at *
  linarith

private theorem bounded_nat_range_maximum (f : ℕ → ℕ) (R : ℕ) (hf : ∀ n, f n ≤ R) :
    ∃ n, ∀ m, f m ≤ f n := by
  induction R with
  | zero => exact ⟨0, fun m => by have := hf m; omega⟩
  | succ R ih =>
    by_cases he : ∃ n, f n = R+1
    · obtain ⟨n, hn⟩ := he
      exact ⟨n, fun m => by rw [hn]; exact hf m⟩
    · apply ih
      intro n
      have hne : f n ≠ R+1 := fun h => he ⟨n,h⟩
      have := hf n
      omega

private theorem path_depth_sum
    (T S : List Bool → upperInterval) (u v : ℕ → List Bool) (z : ℝ)
    (hp : upperPath T S u v z) : ∀ n, (u n).length + (v n).length = n := by
  intro n
  induction n with
  | zero => simp [hp.1, hp.2.1]
  | succ n ih =>
    rcases hp.2.2.2 n with ⟨_, b, hu, hv⟩ | ⟨_, b, hv, hu⟩
    · simp only [hu, hv, List.length_append, List.length_singleton]
      omega
    · simp only [hu, hv, List.length_append, List.length_singleton]
      omega

private theorem path_left_depth_monotone
    (T S : List Bool → upperInterval) (u v : ℕ → List Bool) (z : ℝ)
    (hp : upperPath T S u v z) : Monotone (fun n => (u n).length) := by
  apply monotone_nat_of_le_succ
  intro n
  rcases hp.2.2.2 n with ⟨_, b, hu, _⟩ | ⟨_, b, _, hu⟩
  · simp [hu]
  · simp [hu]

private theorem path_left_depth_cofinal
    (T S : List Bool → upperInterval) (hT : upperNormalTree T) (mS : upperMesh S)
    (u v : ℕ → List Bool) (z : ℝ) (hp : upperPath T S u v z) :
    ∀ k : ℕ, ∃ n : ℕ, k ≤ (u n).length := by
  by_contra hbad
  push_neg at hbad
  obtain ⟨k,hk⟩ := hbad
  obtain ⟨N,hN⟩ := bounded_nat_range_maximum (fun n => (u n).length) k (fun n => (hk n).le)
  have hstable : ∀ n, N ≤ n → u n = u N := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => rfl
    | succ n hn ih =>
      rcases hp.2.2.2 n with ⟨_, b, hu, _⟩ | ⟨_, b, _, hu⟩
      · have hlen := hN (n+1)
        simp only [hu, ih, List.length_append, List.length_singleton] at hlen
        omega
      · exact hu.trans ih
  have hc : 0 < upperLength (T (u N)) := normal_tree_length_positive T hT _
  obtain ⟨M,hM⟩ := mS (upperLength (T (u N))/2) (by linarith)
  let n := max N (M+(u N).length)
  have hnN : N ≤ n := le_max_left _ _
  have hnM : M+(u N).length ≤ n := le_max_right _ _
  have hsum := path_depth_sum T S u v z hp n
  rw [hstable n hnN] at hsum
  have hvm : M ≤ (v n).length := by omega
  have hsmall := hM (v n) hvm
  rcases hp.2.2.2 n with ⟨_, b, hu, _⟩ | ⟨hle, b, _, hu⟩
  · have hlen := hN (n+1)
    simp only [hu, hstable n hnN, List.length_append, List.length_singleton] at hlen
    omega
  · rw [hstable n hnN] at hle
    linarith

private theorem path_swap
    (T S : List Bool → upperInterval) (u v : ℕ → List Bool) (z : ℝ)
    (hp : upperPath T S u v z) : upperPath S T v u z := by
  refine ⟨hp.2.1, hp.1, ?_, ?_⟩
  · intro n
    simpa only [upperDerived, add_comm, min_comm] using hp.2.2.1 n
  · intro n
    exact (hp.2.2.2 n).symm

private theorem mesh_along_cofinal_path
    (T S : List Bool → upperInterval) (hT : upperNormalTree T) (mT : upperMesh T)
    (u v : ℕ → List Bool) (z : ℝ) (hp : upperPath T S u v z)
    (hc : ∀ k : ℕ, ∃ n : ℕ, k ≤ (u n).length) :
    Tendsto (fun n => upperLength (T (u n))) atTop (nhds 0) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨M,hM⟩ := mT (ε/2) (by linarith)
  obtain ⟨N,hN⟩ := hc M
  refine ⟨N, ?_⟩
  intro n hn
  have hdepth := le_trans hN (path_left_depth_monotone T S u v z hp hn)
  have hlength := hM (u n) hdepth
  rw [Real.dist_eq, sub_zero, abs_of_pos (normal_tree_length_positive T hT _)]
  linarith

theorem solution (T S : List Bool → upperInterval) (hT : upperNormalTree T) (hS : upperNormalTree S)
    (mT : upperMesh T) (mS : upperMesh S) (u v : ℕ → List Bool) (z : ℝ)
    (hp : upperPath T S u v z) :
    Tendsto (fun n => upperLength (T (u n))) atTop (nhds 0) ∧
    Tendsto (fun n => upperLength (S (v n))) atTop (nhds 0) := by
  have hs := path_swap T S u v z hp
  exact ⟨mesh_along_cofinal_path T S hT mT u v z hp (path_left_depth_cofinal T S hT mS u v z hp),
    mesh_along_cofinal_path S T hS mS v u z hs (path_left_depth_cofinal S T hS mT v u z hs)⟩
