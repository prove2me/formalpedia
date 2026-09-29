-- Prove2me | solution 1 for Freiman.upper_path_limit
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T21:20:30.661718+00:00
-- url     : https://prove2.me/submissions/16163079-2d83-48aa-9939-8eee0f721e2c

import Definitions.Def_Freiman_upperModel

open Freiman Filter

private theorem normal_tree_length_positive
    (T : List Bool → upperInterval) (hT : upperNormalTree T) (w : List Bool) :
    0 < upperLength (T w) := by
  rcases hT w with ⟨hl, hr, hg, hpl, hpr, _, _⟩
  unfold upperLength at *
  linarith

private theorem normal_tree_child_subset
    (T : List Bool → upperInterval) (hT : upperNormalTree T) (w : List Bool) (b : Bool) :
    upperIntervalSet (T (w ++ [b])) ⊆ upperIntervalSet (T w) := by
  rcases hT w with ⟨hl, hr, hg, hpl, hpr, _, _⟩
  unfold upperLength at *
  intro x hx
  cases b
  · change (T (w ++ [false])).left ≤ x ∧ x ≤ (T (w ++ [false])).right at hx
    change (T w).left ≤ x ∧ x ≤ (T w).right
    constructor <;> linarith [hx.1,hx.2]
  · change (T (w ++ [true])).left ≤ x ∧ x ≤ (T (w ++ [true])).right at hx
    change (T w).left ≤ x ∧ x ≤ (T w).right
    constructor <;> linarith [hx.1,hx.2]

private theorem normal_tree_descendant_subset
    (T : List Bool → upperInterval) (hT : upperNormalTree T) (w v : List Bool) :
    upperIntervalSet (T (w ++ v)) ⊆ upperIntervalSet (T w) := by
  induction v generalizing w with
  | nil => simp
  | cons b v ih =>
    have h₁ := ih (w ++ [b])
    have h₂ := normal_tree_child_subset T hT w b
    simpa only [List.append_assoc, List.singleton_append] using h₁.trans h₂

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

private theorem path_swap
    (T S : List Bool → upperInterval) (u v : ℕ → List Bool) (z : ℝ)
    (hp : upperPath T S u v z) : upperPath S T v u z := by
  refine ⟨hp.2.1, hp.1, ?_, ?_⟩
  · intro n
    simpa only [upperDerived, add_comm, min_comm] using hp.2.2.1 n
  · intro n
    exact (hp.2.2.2 n).symm

private theorem shrinking_path_depth_cofinal
    (T S : List Bool → upperInterval) (hT : upperNormalTree T)
    (u v : ℕ → List Bool) (z : ℝ) (hp : upperPath T S u v z)
    (hlim : Tendsto (fun n => upperLength (T (u n))) atTop (nhds 0)) :
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
  have hc := normal_tree_length_positive T hT (u N)
  obtain ⟨M,hM⟩ := Metric.tendsto_atTop.mp hlim (upperLength (T (u N))/2) (by linarith)
  have hsmall := hM (max N M) (le_max_right _ _)
  rw [hstable _ (le_max_left _ _), Real.dist_eq, sub_zero, abs_of_pos hc] at hsmall
  linarith

private theorem path_intervals_nested
    (T S : List Bool → upperInterval) (hT : upperNormalTree T)
    (u v : ℕ → List Bool) (z : ℝ) (hp : upperPath T S u v z) :
    Antitone (fun n => upperIntervalSet (T (u n))) := by
  apply antitone_nat_of_succ_le
  intro n
  rcases hp.2.2.2 n with ⟨_, b, hu, _⟩ | ⟨_, b, _, hu⟩
  · rw [hu]
    exact normal_tree_child_subset T hT _ _
  · rw [hu]

private theorem path_intersection_exists
    (T S : List Bool → upperInterval) (hT : upperNormalTree T)
    (u v : ℕ → List Bool) (z : ℝ) (hp : upperPath T S u v z) :
    ∃ x : ℝ, ∀ n, x ∈ upperIntervalSet (T (u n)) := by
  have hnon : ∀ n, (T (u n)).left ≤ (T (u n)).right := by
    intro n
    have ht := normal_tree_length_positive T hT (u n)
    unfold upperLength at ht
    linarith
  have ht := ciSup_mem_iInter_Icc_of_antitone_Icc (path_intervals_nested T S hT u v z hp) hnon
  exact ⟨⨆ n, (T (u n)).left, Set.mem_iInter.mp ht⟩

private theorem path_intersection_in_tree
    (T : List Bool → upperInterval) (hT : upperNormalTree T) (u : ℕ → List Bool)
    (hcofinal : ∀ k : ℕ, ∃ n : ℕ, k ≤ (u n).length) (x : ℝ)
    (hx : ∀ n, x ∈ upperIntervalSet (T (u n))) : x ∈ upperTreeSet T := by
  intro k
  obtain ⟨n,hn⟩ := hcofinal k
  refine ⟨(u n).take k, ?_, ?_⟩
  · simp only [List.length_take, Nat.min_eq_left hn]
  · have hs := normal_tree_descendant_subset T hT ((u n).take k) ((u n).drop k)
    rw [List.take_append_drop] at hs
    exact hs (hx n)

private theorem derived_sum_bounds (C D : upperInterval) (z : ℝ) (hz : z ∈ upperDerived C D) :
    C.left + D.left ≤ z ∧ z ≤ C.right + D.right := by
  have h₁ := min_le_left (upperLength C) (upperLength D)
  have h₂ := min_le_right (upperLength C) (upperLength D)
  unfold upperLength at h₁ h₂
  rcases hz with hz | hz
  · simp only [Set.mem_Icc, upperLength] at hz
    exact ⟨hz.1, by linarith [hz.2]⟩
  · simp only [Set.mem_Icc, upperLength] at hz
    exact ⟨by linarith [hz.1], hz.2⟩

theorem solution (T S : List Bool → upperInterval) (hT : upperNormalTree T) (hS : upperNormalTree S)
    (mT : upperMesh T) (mS : upperMesh S) (u v : ℕ → List Bool) (z : ℝ)
    (hp : upperPath T S u v z)
    (hlim : Tendsto (fun n => upperLength (T (u n))) atTop (nhds 0) ∧
      Tendsto (fun n => upperLength (S (v n))) atTop (nhds 0)) :
    z ∈ upperSumSet (upperTreeSet T) (upperTreeSet S) := by
  have hs := path_swap T S u v z hp
  obtain ⟨x,hx⟩ := path_intersection_exists T S hT u v z hp
  obtain ⟨y,hy⟩ := path_intersection_exists S T hS v u z hs
  have hxT := path_intersection_in_tree T hT u
    (shrinking_path_depth_cofinal T S hT u v z hp hlim.1) x hx
  have hyS := path_intersection_in_tree S hS v
    (shrinking_path_depth_cofinal S T hS v u z hs hlim.2) y hy
  have hbound : ∀ n, |z-(x+y)| ≤ upperLength (T (u n)) + upperLength (S (v n)) := by
    intro n
    have hxₙ := hx n
    have hyₙ := hy n
    have hzₙ := derived_sum_bounds (T (u n)) (S (v n)) z (hp.2.2.1 n)
    change (T (u n)).left ≤ x ∧ x ≤ (T (u n)).right at hxₙ
    change (S (v n)).left ≤ y ∧ y ≤ (S (v n)).right at hyₙ
    apply abs_le.mpr
    unfold upperLength
    constructor <;> linarith [hxₙ.1,hxₙ.2,hyₙ.1,hyₙ.2,hzₙ.1,hzₙ.2]
  have hsumlim : Tendsto (fun n => upperLength (T (u n)) + upperLength (S (v n))) atTop (nhds 0) := by
    simpa only [zero_add] using hlim.1.add hlim.2
  have hz0 : |z-(x+y)| ≤ 0 := ge_of_tendsto hsumlim (Eventually.of_forall hbound)
  exact ⟨x, hxT, y, hyS, sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hz0 (abs_nonneg _)))⟩
